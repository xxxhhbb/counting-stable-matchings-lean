import «CanonicalExtraWitness»

/-!
# The local support/window payment for canonical extra-left men
-/

namespace StableMatchingsJointCharging

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy StableMatchingsE2E

noncomputable section

theorem conditionalPartnerSupport_eq_singleton_of_extra_witness
    {n : Nat} {P : ProfileCode n} {forbidden : Fin n}
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbaseTarget : base.1 m = E.ranked.partner j)
    (Wit : CanonicalExtraLeftWitness P hstable base m forbidden)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (hj : 1 ≤ j.val)
    (hwit : revealed Wit.participant)
    (hleftOwner : revealed (stablePartnerOwner E base.1.toCore
      (leftMarkerIndex j ⟨0, hj⟩))) :
    conditionalPartnerSupport P base.1 revealed m = {base.1 m} := by
  classical
  let h : Fin q := leftMarkerIndex j ⟨0, hj⟩
  let owner : Fin n := stablePartnerOwner E base.1.toCore h
  have hAfter : canonicalRotationAfterIndex P hstable m E Wit.rotation = j :=
    lastIncludedInvolving_afterIndex_eq_center
      P hstable base m E j hbaseTarget Wit.rotation Wit.rotation_last
  apply Finset.eq_singleton_iff_unique_mem.2
  constructor
  · exact Finset.mem_image.2 ⟨base.1,
      base_mem_stableFiber P base.1 revealed base.2, rfl⟩
  · intro w hw
    obtain ⟨nu, hnu, hnuTarget⟩ := Finset.mem_image.1 hw
    have hnuStable : Stable P nu :=
      ((mem_stableFiber_iff P base.1 nu revealed).1 hnu).1
    let nuCoded : CodedStable P := ⟨nu, hnuStable⟩
    obtain ⟨t, ht⟩ := E.complete nu.toCore
      ((stableCode_iff_core P nu).1 hnuStable)
    change nu m = E.ranked.partner t at ht
    have hrNu : Wit.rotation ∈ stableRotationIdeal P hstable nuCoded := by
      simpa [nuCoded] using Wit.forced_in_fiber nu revealed hwit hnu
    have htUpper : t.val ≤ j.val := by
      have htMem := (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable nuCoded m E t (by simpa [nuCoded] using ht)
        Wit.rotation Wit.rotation_involves_target).1 hrNu
      rw [hAfter] at htMem
      exact htMem
    have hcompat : CompatibleOn P.toCore base.1.toCore nu.toCore revealed :=
      (mem_stableFiber_iff_core_compatible P base.1 nu revealed).1 hnu
    have htLowerRaw := lower_marker_forces_index P.toCore E
      base.1.toCore nu.toCore revealed
      ((stableCode_iff_core P base.1).1 base.2) hbaseTarget
      hcompat ht (some (h, owner)) (by
        intro h' p' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        refine ⟨?_, manPartner_stablePartnerOwner E base.1.toCore h, ?_⟩
        · simpa [owner, h] using hleftOwner
        · simp [h, leftMarkerIndex]
          omega)
    have htLower : j.val ≤ t.val := by
      have htLower' : j.val - 1 < t.val := by
        simpa [lowerBoundary, h, leftMarkerIndex] using htLowerRaw
      omega
    have htj : t = j := Fin.eq_of_val_eq (by omega)
    have hpartner : nu m = base.1 m := by
      calc
        nu m = E.ranked.partner t := ht
        _ = E.ranked.partner j := by rw [htj]
        _ = base.1 m := hbaseTarget.symm
    exact hnuTarget.symm.trans hpartner

theorem conditionalPartnerSupport_card_eq_one_of_extra_witness
    {n : Nat} {P : ProfileCode n} {forbidden : Fin n}
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbaseTarget : base.1 m = E.ranked.partner j)
    (Wit : CanonicalExtraLeftWitness P hstable base m forbidden)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (hj : 1 ≤ j.val)
    (hwit : revealed Wit.participant)
    (hleftOwner : revealed (stablePartnerOwner E base.1.toCore
      (leftMarkerIndex j ⟨0, hj⟩))) :
    (conditionalPartnerSupport P base.1 revealed m).card = 1 := by
  rw [conditionalPartnerSupport_eq_singleton_of_extra_witness
    hstable base m E j hbaseTarget Wit revealed hj hwit hleftOwner]
  simp

theorem markerWindowWidth_ge_two_of_right_owner_not_revealed
    {n q : Nat} {P : Profile (Fin n) (Fin n)} {m : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P m)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (hright : 1 ≤ q - (j.val + 1))
    (hnot : ¬ revealed (stablePartnerOwner E base
      (rightMarkerIndex j ⟨0, hright⟩))) :
    2 ≤ markerWindowWidth
      (leftMarkerBits E base revealed j)
      (rightMarkerBits E base revealed j) := by
  let xs := rightMarkerBits E base revealed j
  have hlen : 0 < xs.length := by
    simp [xs]
    omega
  have hhead : xs[0] = false := by
    have hbit : ownerMarkerBit E base revealed
        (rightMarkerIndex j ⟨0, hright⟩) = false := by
      cases hb : ownerMarkerBit E base revealed
          (rightMarkerIndex j ⟨0, hright⟩)
      · rfl
      · exfalso
        apply hnot
        exact (ownerMarkerBit_eq_true_iff E base revealed
          (rightMarkerIndex j ⟨0, hright⟩)).1 hb
    simpa [xs, rightMarkerBits] using hbit
  have hrightWait : 2 ≤ truncatedWait xs := by
    cases hxs : xs with
    | nil => simp [hxs] at hlen
    | cons b bs =>
        have hb : b = false := by simpa [hxs] using hhead
        subst b
        have hbpos := truncatedWait_pos bs
        simp only [truncatedWait]
        omega
  have hleftWait := truncatedWait_pos (leftMarkerBits E base revealed j)
  unfold markerWindowWidth
  change 2 ≤ truncatedWait (leftMarkerBits E base revealed j) +
    truncatedWait xs - 1
  omega

theorem exists_fin_not_mem_of_card_lt {n : Nat}
    (S : Finset (Fin n)) (hcard : S.card < n) :
    ∃ p : Fin n, p ∉ S := by
  classical
  by_contra hnone
  have hall : S = Finset.univ := by
    ext p
    simp only [Finset.mem_univ, iff_true]
    by_contra hp
    exact hnone ⟨p, hp⟩
  rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
  omega

structure ExtraPriorityEmbedding {n : Nat}
    (target witness leftOwner rightOwner : Fin n) where
  embedding : Fin 4 ↪ OtherMen target
  witness_at_zero : (embedding 0).1 = witness
  left_at_zero_or_one : (embedding 0).1 = leftOwner ∨
    (embedding 1).1 = leftOwner
  right_at_three : (embedding 3).1 = rightOwner

theorem exists_extraPriorityEmbedding {n : Nat} (hn : 5 ≤ n)
    (target witness leftOwner rightOwner : Fin n)
    (hwTarget : witness ≠ target) (hlTarget : leftOwner ≠ target)
    (hrTarget : rightOwner ≠ target)
    (hwRight : witness ≠ rightOwner)
    (hlRight : leftOwner ≠ rightOwner) :
    Nonempty (ExtraPriorityEmbedding target witness leftOwner rightOwner) := by
  classical
  by_cases hwl : witness = leftOwner
  · let S1 : Finset (Fin n) := {target, witness, rightOwner}
    have hS1le : S1.card ≤ 3 := by
      have h1 := Finset.card_insert_le target ({witness, rightOwner} : Finset (Fin n))
      have h2 := Finset.card_insert_le witness ({rightOwner} : Finset (Fin n))
      simp only [Finset.card_singleton] at h2
      dsimp [S1]
      omega
    have hS1card : S1.card < n := by omega
    obtain ⟨pad1, hpad1⟩ := exists_fin_not_mem_of_card_lt S1 hS1card
    let S2 : Finset (Fin n) := insert pad1 S1
    have hS2card : S2.card < n := by
      have hle : S2.card ≤ S1.card + 1 := by
        simpa [S2] using Finset.card_insert_le pad1 S1
      omega
    obtain ⟨pad2, hpad2⟩ := exists_fin_not_mem_of_card_lt S2 hS2card
    have hp1Target : pad1 ≠ target := by
      intro heq
      apply hpad1
      simp [S1, heq]
    have hp1Witness : pad1 ≠ witness := by
      intro heq
      apply hpad1
      simp [S1, heq]
    have hp1Right : pad1 ≠ rightOwner := by
      intro heq
      apply hpad1
      simp [S1, heq]
    have hp2Target : pad2 ≠ target := by
      intro heq
      apply hpad2
      simp [S2, S1, heq]
    have hp2Witness : pad2 ≠ witness := by
      intro heq
      apply hpad2
      simp [S2, S1, heq]
    have hp2Right : pad2 ≠ rightOwner := by
      intro heq
      apply hpad2
      simp [S2, S1, heq]
    have hp2Pad1 : pad2 ≠ pad1 := by
      intro heq
      apply hpad2
      simp [S2, heq]
    let e : Fin 4 → OtherMen target := fun i ↦
      ![⟨witness, hwTarget⟩, ⟨pad1, hp1Target⟩,
        ⟨pad2, hp2Target⟩, ⟨rightOwner, hrTarget⟩] i
    have heInj : Function.Injective e := by
      intro i k hik
      fin_cases i <;> fin_cases k <;>
        simp_all [e, hwRight, hp1Witness, hp1Right, hp2Witness,
          hp2Right, hp2Pad1]
    refine ⟨{
      embedding := ⟨e, heInj⟩
      witness_at_zero := by rfl
      left_at_zero_or_one := Or.inl (by simpa [hwl])
      right_at_three := by rfl }⟩
  · let S : Finset (Fin n) := {target, witness, leftOwner, rightOwner}
    have hScard : S.card < n := by
      have h1 := Finset.card_insert_le target
        ({witness, leftOwner, rightOwner} : Finset (Fin n))
      have h2 := Finset.card_insert_le witness
        ({leftOwner, rightOwner} : Finset (Fin n))
      have h3 := Finset.card_insert_le leftOwner
        ({rightOwner} : Finset (Fin n))
      simp only [Finset.card_singleton] at h3
      dsimp [S]
      omega
    obtain ⟨pad, hpad⟩ := exists_fin_not_mem_of_card_lt S hScard
    have hpTarget : pad ≠ target := by
      intro heq
      apply hpad
      simp [S, heq]
    have hpWitness : pad ≠ witness := by
      intro heq
      apply hpad
      simp [S, heq]
    have hpLeft : pad ≠ leftOwner := by
      intro heq
      apply hpad
      simp [S, heq]
    have hpRight : pad ≠ rightOwner := by
      intro heq
      apply hpad
      simp [S, heq]
    let e : Fin 4 → OtherMen target := fun i ↦
      ![⟨witness, hwTarget⟩, ⟨leftOwner, hlTarget⟩,
        ⟨pad, hpTarget⟩, ⟨rightOwner, hrTarget⟩] i
    have heInj : Function.Injective e := by
      intro i k hik
      fin_cases i <;> fin_cases k <;>
        simp_all [e, hwl, hwRight, hlRight, hpWitness, hpLeft, hpRight]
    refine ⟨{
      embedding := ⟨e, heInj⟩
      witness_at_zero := by rfl
      left_at_zero_or_one := Or.inr (by rfl)
      right_at_three := by rfl }⟩

structure CanonicalExtraLocalData {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) where
  leftTwo : 2 ≤ (D.center base m).val
  rightTwo : 2 ≤ D.q m - ((D.center base m).val + 1)
  witness : CanonicalExtraLeftWitness P hstable base m
    (stablePartnerOwner (D.enumeration m) base.1.toCore
      (rightMarkerIndex (D.center base m) ⟨0, by omega⟩))
  priorityEmbedding : ExtraPriorityEmbedding m witness.participant
    (stablePartnerOwner (D.enumeration m) base.1.toCore
      (leftMarkerIndex (D.center base m) ⟨0, by omega⟩))
    (stablePartnerOwner (D.enumeration m) base.1.toCore
      (rightMarkerIndex (D.center base m) ⟨0, by omega⟩))

theorem exists_canonicalExtraLocalData {n : Nat} {P : ProfileCode n}
    (hn : 5 ≤ n) (D : StaticWindowData P)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) (m : Fin n)
    (hextra : canonicalExtraLeft P hstable base m) :
    Nonempty (CanonicalExtraLocalData D hstable base m) := by
  classical
  let E := D.enumeration m
  let j := D.center base m
  have hdeep := hextra.1
  have hcards :
      2 ≤ (excludedInvolvingRotations P hstable base m).card ∧
      2 ≤ (includedInvolvingRotations P hstable base m).card := by
    simp only [canonicalShallow, not_or, not_le] at hdeep
    omega
  have hleft : 2 ≤ j.val := by
    rw [← card_excludedInvolvingRotations_eq_center
      P hstable base m E j (D.center_spec base m)]
    exact hcards.1
  have hright : 2 ≤ D.q m - (j.val + 1) := by
    rw [← card_includedInvolvingRotations_eq_rightLen
      P hstable base m E j (D.center_spec base m)]
    exact hcards.2
  let leftIdx : Fin (D.q m) := leftMarkerIndex j ⟨0, by omega⟩
  let rightIdx : Fin (D.q m) := rightMarkerIndex j ⟨0, by omega⟩
  let leftOwner := stablePartnerOwner E base.1.toCore leftIdx
  let rightOwner := stablePartnerOwner E base.1.toCore rightIdx
  have hleftTarget : leftOwner ≠ m := by
    dsimp [leftOwner]
    apply stablePartnerOwner_ne_target E base.1.toCore
      (D.center_spec base m)
    intro heq
    have hval := congrArg Fin.val heq
    simp [leftIdx, leftMarkerIndex, j] at hval
    omega
  have hrightTarget : rightOwner ≠ m := by
    dsimp [rightOwner]
    apply stablePartnerOwner_ne_target E base.1.toCore
      (D.center_spec base m)
    intro heq
    have hval := congrArg Fin.val heq
    simp [rightIdx, rightMarkerIndex, j] at hval
  have hleftRight : leftOwner ≠ rightOwner := by
    intro heq
    have hidx := stablePartnerOwner_injective E base.1.toCore heq
    have hval := congrArg Fin.val hidx
    simp [leftIdx, rightIdx, leftMarkerIndex, rightMarkerIndex, j] at hval
  obtain ⟨Wit⟩ := exists_canonicalExtraLeftWitness
    P hstable base m rightOwner hrightTarget hextra
  obtain ⟨Emb⟩ := exists_extraPriorityEmbedding hn m Wit.participant
    leftOwner rightOwner Wit.participant_ne hleftTarget hrightTarget
    Wit.participant_ne_forbidden hleftRight
  refine ⟨{
    leftTwo := hleft
    rightTwo := hright
    witness := ?_
    priorityEmbedding := ?_ }⟩
  · simpa [E, j, rightIdx, rightOwner] using Wit
  · simpa [E, j, leftIdx, rightIdx, leftOwner, rightOwner] using Emb

theorem listPrefixFiber_filter_eq_append_singleton_local
    {A J B : Type*} [DecidableEq A] [DecidableEq J] [DecidableEq B]
    (s : Finset A) (code : A → J → B) (seen : List J)
    (i : J) (base : A) :
    (listPrefixFiber s code seen base).filter
        (fun x ↦ code x i = code base i) =
      listPrefixFiber s code (seen ++ [i]) base := by
  ext x
  simp only [Finset.mem_filter, mem_listPrefixFiber_iff]
  constructor
  · rintro ⟨⟨hxs, hseen⟩, hi⟩
    refine ⟨hxs, ?_⟩
    intro j hj
    rw [List.mem_append] at hj
    rcases hj with hj | hj
    · exact hseen j hj
    · have hji : j = i := by simpa using hj
      subst j
      exact hi
  · rintro ⟨hxs, hall⟩
    refine ⟨⟨hxs, ?_⟩, ?_⟩
    · intro j hj
      exact hall j (List.mem_append_left [i] hj)
    · exact hall i (by simp)

theorem suffix_path_gap_le_full_path_gap
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (seen pref rest : List (Fin n)) :
    prefixWindowPathBudget P D.selector base (seen ++ pref) rest -
        revealPathBudget
          (listPrefixFiber (stableSet P) (fun mu p ↦ mu p)
            (seen ++ pref) base.1)
          (fun mu p ↦ mu p) base.1 rest ≤
      prefixWindowPathBudget P D.selector base seen (pref ++ rest) -
        revealPathBudget
          (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base.1)
          (fun mu p ↦ mu p) base.1 (pref ++ rest) := by
  induction pref generalizing seen with
  | nil => simp
  | cons a pref ih =>
      have hhead := revealPathBudget_le_prefixWindowPathBudget
        P D.selector base seen [a]
      have htail := ih (seen ++ [a])
      simp only [prefixWindowPathBudget, revealPathBudget, List.cons_append,
        ] at hhead ⊢
      rw [listPrefixFiber_filter_eq_append_singleton_local] at ⊢
      rw [show seen ++ a :: pref = (seen ++ [a]) ++ pref by simp]
      rw [D.selector_width seen a base]
      norm_num at hhead
      linarith

theorem supportWindowPathGap_ge_log_two_of_extra_conditions
    {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (L : CanonicalExtraLocalData D hstable base m)
    (priority : Fin n → I)
    (hwit : LexUnitRevealedBefore priority m L.witness.participant)
    (hleft : LexUnitRevealedBefore priority m
      (stablePartnerOwner (D.enumeration m) base.1.toCore
        (leftMarkerIndex (D.center base m) ⟨0, by
          have := L.leftTwo
          omega⟩)))
    (hright : ¬ LexUnitRevealedBefore priority m
      (stablePartnerOwner (D.enumeration m) base.1.toCore
        (rightMarkerIndex (D.center base m) ⟨0, by
          have := L.rightTwo
          omega⟩))) :
    Real.log 2 ≤ supportWindowPathGap D priority base.1 := by
  classical
  let order := priorityOrder priority
  let idx : Fin n := order.symm m
  let all := List.ofFn order
  let seen := all.take idx.val
  let rest := all.drop (idx.val + 1)
  have hidx : idx.val < all.length := by simp [all, idx]
  have hget : all[idx.val] = m := by simp [all, idx, order]
  have hdecomp : all = seen ++ m :: rest := by
    calc
      all = all.take idx.val ++ all.drop idx.val :=
        (List.take_append_drop idx.val all).symm
      _ = seen ++ m :: rest := by
        rw [List.drop_eq_getElem_cons hidx, hget]
  have hrevealed : listRevealed seen = LexUnitRevealedBefore priority m := by
    funext p
    apply propext
    change p ∈ seen ↔ _
    rw [show seen = (List.ofFn order).take idx.val by rfl]
    rw [mem_take_ofFn_perm_iff]
    change (order.symm p).val < (order.symm m).val ↔ _
    exact fixedOrderRevealed_priorityOrder_target_iff priority m p
  have hsupport :
      (conditionalPartnerSupport P base.1 (listRevealed seen) m).card = 1 := by
    apply conditionalPartnerSupport_card_eq_one_of_extra_witness
      hstable base m (D.enumeration m) (D.center base m)
      (D.center_spec base m) L.witness (listRevealed seen)
      (by have := L.leftTwo; omega)
    · simpa [hrevealed] using hwit
    · simpa [hrevealed] using hleft
  have hwidth : 2 ≤ markerWindowWidth
      (leftMarkerBits (D.enumeration m) base.1.toCore
        (listRevealed seen) (D.center base m))
      (rightMarkerBits (D.enumeration m) base.1.toCore
        (listRevealed seen) (D.center base m)) := by
    apply markerWindowWidth_ge_two_of_right_owner_not_revealed
      (D.enumeration m) base.1.toCore (D.center base m)
      (listRevealed seen) (by have := L.rightTwo; omega)
    simpa [hrevealed] using hright
  have hnode := prefixWindow_sub_reveal_ge_log_two_of_head
    D base seen m rest hsupport hwidth
  have hlocalize := suffix_path_gap_le_full_path_gap
    D base [] seen (m :: rest)
  simp only [List.nil_append] at hlocalize
  rw [← hdecomp] at hlocalize
  have hlocalize' :
      prefixWindowPathBudget P D.selector base seen (m :: rest) -
          revealPathBudget
            (listPrefixFiber (stableSet P) (fun mu p ↦ mu p) seen base.1)
            (fun mu p ↦ mu p) base.1 (m :: rest) ≤
        prefixWindowPathBudget P D.selector base [] all -
          revealPathBudget (stableSet P) (fun mu p ↦ mu p) base.1 all := by
    simpa [listPrefixFiber] using hlocalize
  unfold supportWindowPathGap
  simp only [base.2, dif_pos]
  change Real.log 2 ≤
    prefixWindowPathBudget P D.selector base [] all -
      revealPathBudget (stableSet P) (fun mu p ↦ mu p) base.1 all
  linarith

end

end StableMatchingsJointCharging
