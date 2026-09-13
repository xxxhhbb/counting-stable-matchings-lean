import «CanonicalChargeAverage»

/-!
# Canonical rotation cuts versus exact stable-partner indices

For one man, canonical rotations are identified with all adjacent gaps in
the exact ranked list of stable partners.  Consequently the number of
excluded involving rotations is the current partner index, while the number
of included involving rotations is the number of indices to its right.
-/

namespace StableMatchingsJointCharging

open StableMatchings355 StableMatchingsE2E

noncomputable section

def allInvolvingRotations {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n) : Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact Finset.univ.filter fun r ↦
    canonicalRotationInvolvesMan P hstable m r

@[simp] theorem mem_allInvolvingRotations_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n) (r : CanonicalRotation P) :
    r ∈ allInvolvingRotations P hstable m ↔
      canonicalRotationInvolvesMan P hstable m r := by
  classical
  simp [allInvolvingRotations]

noncomputable def canonicalRotationAfterIndex {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (r : CanonicalRotation P) : Fin q :=
  Classical.choose (E.complete (rotationAfter P hstable r).1.toCore
    ((stableCode_iff_core P (rotationAfter P hstable r).1).1
      (rotationAfter P hstable r).2))

theorem canonicalRotationAfterIndex_spec {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (r : CanonicalRotation P) :
    (rotationAfter P hstable r).1 m =
      E.ranked.partner (canonicalRotationAfterIndex P hstable m E r) := by
  exact Classical.choose_spec (E.complete
    (rotationAfter P hstable r).1.toCore
    ((stableCode_iff_core P (rotationAfter P hstable r).1).1
      (rotationAfter P hstable r).2))

theorem rotationAfter_le_rotationBefore_of_lt_canonical {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    {r s : CanonicalRotation P} (hrs : r < s) :
    rotationAfter P hstable r ≤ rotationBefore P hstable s := by
  let e := stableBirkhoffLowerSet P hstable
  change e.symm (closedRotationLowerSet r) ≤
    e.symm (strictRotationLowerSet s)
  rw [e.symm.le_iff_le]
  intro t ht
  exact ht.trans_lt hrs

theorem canonicalRotationAfterIndex_injective_on_involving {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m) :
    Set.InjOn (canonicalRotationAfterIndex P hstable m E)
      {r | canonicalRotationInvolvesMan P hstable m r} := by
  intro r hr s hs hindex
  rcases canonicalRotations_involving_man_comparable
      P hstable m hr hs with hrs | hsr
  · rcases hrs.eq_or_lt with rfl | hrslt
    · rfl
    · have hle := rotationAfter_le_rotationBefore_of_lt_canonical
        P hstable hrslt
      have hbeforeLe : P.manRank m ((rotationBefore P hstable s).1 m) ≤
          P.manRank m ((rotationAfter P hstable r).1 m) := hle m
      have hstrict := involved_manRank_strict P hstable m s hs
      have hafterNe : (rotationAfter P hstable r).1 m ≠
          (rotationAfter P hstable s).1 m := by
        intro heq
        have hrankEq := congrArg (P.manRank m) heq
        omega
      exact False.elim (hafterNe (by
        rw [canonicalRotationAfterIndex_spec P hstable m E r,
          canonicalRotationAfterIndex_spec P hstable m E s, hindex]))
  · rcases hsr.eq_or_lt with hsrEq | hsrlt
    · exact hsrEq.symm
    · have hle := rotationAfter_le_rotationBefore_of_lt_canonical
        P hstable hsrlt
      have hbeforeLe : P.manRank m ((rotationBefore P hstable r).1 m) ≤
          P.manRank m ((rotationAfter P hstable s).1 m) := hle m
      have hstrict := involved_manRank_strict P hstable m r hr
      have hafterNe : (rotationAfter P hstable r).1 m ≠
          (rotationAfter P hstable s).1 m := by
        intro heq
        have hrankEq := congrArg (P.manRank m) heq
        omega
      exact False.elim (hafterNe (by
        rw [canonicalRotationAfterIndex_spec P hstable m E r,
          canonicalRotationAfterIndex_spec P hstable m E s, hindex]))

theorem mem_rotationIdeal_iff_center_le_afterIndex {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j)
    (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable m r) :
    r ∈ stableRotationIdeal P hstable base ↔
      j.val ≤ (canonicalRotationAfterIndex P hstable m E r).val := by
  rw [mem_rotationIdeal_iff_manRank_le_after_of_involves
    P hstable base m r hinv]
  rw [hbase, canonicalRotationAfterIndex_spec P hstable m E r]
  let i := canonicalRotationAfterIndex P hstable m E r
  have hrankIff : P.manRank m (E.ranked.partner j) <
      P.manRank m (E.ranked.partner i) ↔ j.val < i.val := by
    exact E.ranked.rank_spec j i
  constructor
  · intro hle
    rcases hle.eq_or_lt with heq | hlt
    · have hpartner : E.ranked.partner j = E.ranked.partner i :=
        (P.manRank m).injective heq
      exact (Fin.eq_of_val_eq (congrArg Fin.val
        (E.ranked.injective hpartner))).le
    · exact (hrankIff.mp hlt).le
  · intro hji
    rcases hji.eq_or_lt with hjiEq | hjiLt
    · have hfin : j = i := Fin.eq_of_val_eq hjiEq
      exact (congrArg (fun t : Fin q ↦
        P.manRank m (E.ranked.partner t)) hfin).le
    · exact (hrankIff.mpr hjiLt).le

theorem canonicalRotationAfterIndex_lt_last {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable m r) :
    (canonicalRotationAfterIndex P hstable m E r).val + 1 < q := by
  obtain ⟨b, hb⟩ := E.complete (rotationBefore P hstable r).1.toCore
    ((stableCode_iff_core P (rotationBefore P hstable r).1).1
      (rotationBefore P hstable r).2)
  have hbefore : (rotationBefore P hstable r).1 m = E.ranked.partner b := hb
  have hstrict := involved_manRank_strict P hstable m r hinv
  rw [canonicalRotationAfterIndex_spec P hstable m E r, hbefore] at hstrict
  have hindex := (E.ranked.rank_spec
    (canonicalRotationAfterIndex P hstable m E r) b).mp hstrict
  omega

set_option maxHeartbeats 800000 in
theorem exists_involving_rotation_with_afterIndex {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (i : Fin q) (hi : i.val + 1 < q) :
    ∃ r : CanonicalRotation P,
      canonicalRotationInvolvesMan P hstable m r ∧
      canonicalRotationAfterIndex P hstable m E r = i := by
  let ip : Fin q := ⟨i.val + 1, hi⟩
  obtain ⟨betterCore, hbetterStable, hbetterPartner⟩ := E.realized i
  obtain ⟨worseCore, hworseStable, hworsePartner⟩ := E.realized ip
  let betterCode := MatchingCode.ofCore betterCore
  let worseCode := MatchingCode.ofCore worseCore
  have hbetterCode : Stable P betterCode := by
    apply (stableCode_iff_core P betterCode).2
    simpa [betterCode, MatchingCode.toCore, MatchingCode.ofCore] using
      hbetterStable
  have hworseCode : Stable P worseCode := by
    apply (stableCode_iff_core P worseCode).2
    simpa [worseCode, MatchingCode.toCore, MatchingCode.ofCore] using
      hworseStable
  let better : CodedStable P := ⟨betterCode, hbetterCode⟩
  let worse : CodedStable P := ⟨worseCode, hworseCode⟩
  have hbetter : better.1 m = E.ranked.partner i := by
    simpa [better, betterCode, MatchingCode.ofCore] using hbetterPartner
  have hworse : worse.1 m = E.ranked.partner ip := by
    simpa [worse, worseCode, MatchingCode.ofCore] using hworsePartner
  have hrank : P.manRank m (better.1 m) < P.manRank m (worse.1 m) := by
    rw [hbetter, hworse]
    exact (E.ranked.rank_spec i ip).2 (by simp [ip])
  let lo := better ⊓ worse
  let hiMatch := better ⊔ worse
  have hloPartner : lo.1 m = E.ranked.partner ip := by
    apply (P.manRank m).injective
    rw [show P.manRank m (lo.1 m) =
      max (P.manRank m (better.1 m)) (P.manRank m (worse.1 m)) by
        exact manRank_inf P better worse m]
    rw [max_eq_right hrank.le, ← hworse]
  have hhiPartner : hiMatch.1 m = E.ranked.partner i := by
    apply (P.manRank m).injective
    rw [show P.manRank m (hiMatch.1 m) =
      min (P.manRank m (better.1 m)) (P.manRank m (worse.1 m)) by
        exact manRank_sup P better worse m]
    rw [min_eq_left hrank.le, ← hbetter]
  have hlohi : lo ≤ hiMatch :=
    (inf_le_left : better ⊓ worse ≤ better).trans
      (le_sup_left : better ≤ better ⊔ worse)
  have hpartnerNe : lo.1 m ≠ hiMatch.1 m := by
    rw [hloPartner, hhiPartner]
    intro h
    have hipi : ip = i := E.ranked.injective h
    have hval := congrArg Fin.val hipi
    simp only [ip] at hval
    omega
  obtain ⟨r, hrlo, hrhi, hinv⟩ :=
    exists_involving_rotation_in_ideal_diff_of_partner_ne
      P hstable lo hiMatch m hlohi hpartnerNe
  refine ⟨r, hinv, ?_⟩
  let t := canonicalRotationAfterIndex P hstable m E r
  have hit : i.val ≤ t.val :=
    (mem_rotationIdeal_iff_center_le_afterIndex
      P hstable hiMatch m E i hhiPartner r hinv).1 hrhi
  have hnipt : ¬ ip.val ≤ t.val := by
    intro hle
    exact hrlo ((mem_rotationIdeal_iff_center_le_afterIndex
      P hstable lo m E ip hloPartner r hinv).2 hle)
  have hval : t.val = i.val := by
    simp only [ip] at hnipt
    omega
  exact Fin.eq_of_val_eq hval

noncomputable def canonicalInvolvingRotationIndexEquiv {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m) :
    ↥(allInvolvingRotations P hstable m) ≃ Fin (q - 1) := by
  let f : ↥(allInvolvingRotations P hstable m) → Fin (q - 1) := fun r ↦
    ⟨(canonicalRotationAfterIndex P hstable m E r.1).val, by
      have hlast := canonicalRotationAfterIndex_lt_last
        P hstable m E r.1
          ((mem_allInvolvingRotations_iff P hstable m r.1).1 r.2)
      omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro r s h
    apply Subtype.ext
    apply canonicalRotationAfterIndex_injective_on_involving
      P hstable m E
    · exact (mem_allInvolvingRotations_iff P hstable m r.1).1 r.2
    · exact (mem_allInvolvingRotations_iff P hstable m s.1).1 s.2
    · have hv := congrArg Fin.val h
      change (canonicalRotationAfterIndex P hstable m E r.1).val =
        (canonicalRotationAfterIndex P hstable m E s.1).val at hv
      exact Fin.eq_of_val_eq hv
  · intro i
    have hiq : i.val < q := by omega
    let iq : Fin q := ⟨i.val, hiq⟩
    have hiNext : iq.val + 1 < q := by
      have := i.2
      simp only [iq]
      omega
    obtain ⟨r, hinv, hrindex⟩ :=
      exists_involving_rotation_with_afterIndex
        P hstable m E iq hiNext
    refine ⟨⟨r, (mem_allInvolvingRotations_iff
      P hstable m r).2 hinv⟩, ?_⟩
    exact Fin.eq_of_val_eq (by
      change (canonicalRotationAfterIndex P hstable m E r).val = i.val
      rw [hrindex])

@[simp] theorem canonicalInvolvingRotationIndexEquiv_apply_val {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (r : ↥(allInvolvingRotations P hstable m)) :
    (canonicalInvolvingRotationIndexEquiv P hstable m E r).val =
      (canonicalRotationAfterIndex P hstable m E r.1).val := by
  rfl

noncomputable def excludedInvolvingRotationIndexEquiv {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j) :
    ↥(excludedInvolvingRotations P hstable base m) ≃ Fin j.val := by
  let allEquiv := canonicalInvolvingRotationIndexEquiv P hstable m E
  let f : ↥(excludedInvolvingRotations P hstable base m) → Fin j.val :=
    fun r ↦ ⟨(canonicalRotationAfterIndex P hstable m E r.1).val, by
      have hrInfo := (mem_excludedInvolvingRotations_iff
        P hstable base m r.1).1 r.2
      have hnot : ¬ j.val ≤
          (canonicalRotationAfterIndex P hstable m E r.1).val := by
        intro hle
        exact hrInfo.1
          ((mem_rotationIdeal_iff_center_le_afterIndex
            P hstable base m E j hbase r.1 hrInfo.2).2 hle)
      exact Nat.lt_of_not_ge hnot⟩
  apply Equiv.ofBijective f
  constructor
  · intro r s h
    apply Subtype.ext
    apply canonicalRotationAfterIndex_injective_on_involving P hstable m E
    · exact ((mem_excludedInvolvingRotations_iff
        P hstable base m r.1).1 r.2).2
    · exact ((mem_excludedInvolvingRotations_iff
        P hstable base m s.1).1 s.2).2
    · have hv := congrArg Fin.val h
      change (canonicalRotationAfterIndex P hstable m E r.1).val =
        (canonicalRotationAfterIndex P hstable m E s.1).val at hv
      exact Fin.eq_of_val_eq hv
  · intro i
    have hiLast : i.val < q - 1 := by omega
    let t : Fin (q - 1) := ⟨i.val, hiLast⟩
    let rAll := allEquiv.symm t
    have hrInv : canonicalRotationInvolvesMan P hstable m rAll.1 :=
      (mem_allInvolvingRotations_iff P hstable m rAll.1).1 rAll.2
    have hindexVal :
        (canonicalRotationAfterIndex P hstable m E rAll.1).val = i.val := by
      have happly := canonicalInvolvingRotationIndexEquiv_apply_val
        P hstable m E rAll
      rw [allEquiv.apply_symm_apply t] at happly
      exact happly.symm
    have hrNot : rAll.1 ∉ stableRotationIdeal P hstable base := by
      intro hrMem
      have hji := (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable base m E j hbase rAll.1 hrInv).1 hrMem
      rw [hindexVal] at hji
      omega
    refine ⟨⟨rAll.1, (mem_excludedInvolvingRotations_iff
      P hstable base m rAll.1).2 ⟨hrNot, hrInv⟩⟩, ?_⟩
    exact Fin.eq_of_val_eq hindexVal

noncomputable def includedInvolvingRotationIndexEquiv {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j) :
    ↥(includedInvolvingRotations P hstable base m) ≃
      Fin (q - (j.val + 1)) := by
  let allEquiv := canonicalInvolvingRotationIndexEquiv P hstable m E
  let f : ↥(includedInvolvingRotations P hstable base m) →
      Fin (q - (j.val + 1)) := fun r ↦
    ⟨(canonicalRotationAfterIndex P hstable m E r.1).val - j.val, by
      have hrInfo := (mem_includedInvolvingRotations_iff
        P hstable base m r.1).1 r.2
      have hj := (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable base m E j hbase r.1 hrInfo.2).1 hrInfo.1
      have hlast := canonicalRotationAfterIndex_lt_last
        P hstable m E r.1 hrInfo.2
      omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro r s h
    apply Subtype.ext
    apply canonicalRotationAfterIndex_injective_on_involving P hstable m E
    · exact ((mem_includedInvolvingRotations_iff
        P hstable base m r.1).1 r.2).2
    · exact ((mem_includedInvolvingRotations_iff
        P hstable base m s.1).1 s.2).2
    · have hrMem := (mem_includedInvolvingRotations_iff
        P hstable base m r.1).1 r.2
      have hsMem := (mem_includedInvolvingRotations_iff
        P hstable base m s.1).1 s.2
      have hjr := (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable base m E j hbase r.1 hrMem.2).1 hrMem.1
      have hjs := (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable base m E j hbase s.1 hsMem.2).1 hsMem.1
      apply Fin.eq_of_val_eq
      have hv := congrArg Fin.val h
      change (canonicalRotationAfterIndex P hstable m E r.1).val - j.val =
        (canonicalRotationAfterIndex P hstable m E s.1).val - j.val at hv
      omega
  · intro i
    have htLast : j.val + i.val < q - 1 := by
      have := i.2
      omega
    let t : Fin (q - 1) := ⟨j.val + i.val, htLast⟩
    let rAll := allEquiv.symm t
    have hrInv : canonicalRotationInvolvesMan P hstable m rAll.1 :=
      (mem_allInvolvingRotations_iff P hstable m rAll.1).1 rAll.2
    have hindexVal :
        (canonicalRotationAfterIndex P hstable m E rAll.1).val =
          j.val + i.val := by
      have happly := canonicalInvolvingRotationIndexEquiv_apply_val
        P hstable m E rAll
      rw [allEquiv.apply_symm_apply t] at happly
      exact happly.symm
    have hrMem : rAll.1 ∈ stableRotationIdeal P hstable base := by
      apply (mem_rotationIdeal_iff_center_le_afterIndex
        P hstable base m E j hbase rAll.1 hrInv).2
      rw [hindexVal]
      omega
    refine ⟨⟨rAll.1, (mem_includedInvolvingRotations_iff
      P hstable base m rAll.1).2 ⟨hrMem, hrInv⟩⟩, ?_⟩
    exact Fin.eq_of_val_eq (by
      change (canonicalRotationAfterIndex P hstable m E rAll.1).val -
        j.val = i.val
      rw [hindexVal]
      omega)

theorem card_excludedInvolvingRotations_eq_center {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j) :
    (excludedInvolvingRotations P hstable base m).card = j.val := by
  rw [← Fintype.card_coe,
    Fintype.card_congr
      (excludedInvolvingRotationIndexEquiv
        P hstable base m E j hbase), Fintype.card_fin]

theorem card_includedInvolvingRotations_eq_rightLen {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j) :
    (includedInvolvingRotations P hstable base m).card =
      q - (j.val + 1) := by
  rw [← Fintype.card_coe,
    Fintype.card_congr
      (includedInvolvingRotationIndexEquiv
        P hstable base m E j hbase), Fintype.card_fin]

theorem canonicalShallow_iff_center_endpoint {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j) :
    canonicalShallow P hstable base m ↔
      j.val ≤ 1 ∨ q - (j.val + 1) ≤ 1 := by
  rw [canonicalShallow,
    card_excludedInvolvingRotations_eq_center P hstable base m E j hbase,
    card_includedInvolvingRotations_eq_rightLen P hstable base m E j hbase]
  tauto

end

end StableMatchingsJointCharging
