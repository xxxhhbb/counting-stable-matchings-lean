import «CanonicalLocalPayments»

/-!
# A revealed-participant witness for every canonical extra-left charge

The witness is deliberately stated in the exact stable fiber used by the
entropy recursion.  Revealing its partner forces the last included rotation
of the charged man to remain in every compatible stable matching.
-/

namespace StableMatchingsJointCharging

open StableMatchings355 StableMatchingsE2E

noncomputable section

theorem exists_mem_ne_of_two_le_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m : α) (hcard : 2 ≤ S.card) :
    ∃ p ∈ S, p ≠ m := by
  classical
  by_cases hm : m ∈ S
  · have hpos : 0 < (S.erase m).card := by
      rw [Finset.card_erase_of_mem hm]
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    exact ⟨p, Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩
  · have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hnonempty
    exact ⟨p, hp, fun hpm ↦ hm (hpm ▸ hp)⟩

theorem exists_mem_ne_ne_of_three_le_card {α : Type*} [DecidableEq α]
    (S : Finset α) (a b : α) (hcard : 3 ≤ S.card) :
    ∃ p ∈ S, p ≠ a ∧ p ≠ b := by
  classical
  by_contra hnone
  have hsub : S ⊆ ({a, b} : Finset α) := by
    intro p hp
    by_contra hpab
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpab
    exact hnone ⟨p, hp, hpab.1, hpab.2⟩
  have hle := Finset.card_le_card hsub
  have hab : ({a, b} : Finset α).card ≤ 2 := by
    by_cases heq : a = b
    · subst b
      simp
    · simp [heq]
  omega

structure CanonicalExtraLeftWitness {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m forbidden : Fin n) where
  rotation : CanonicalRotation P
  participant : Fin n
  participant_ne : participant ≠ m
  participant_ne_forbidden : participant ≠ forbidden
  rotation_last : IsLastIncludedInvolving P hstable base m rotation
  rotation_mem_base : rotation ∈ stableRotationIdeal P hstable base
  rotation_involves_target :
    canonicalRotationInvolvesMan P hstable m rotation
  forced_in_fiber : ∀ (nu : MatchingCode n)
      (revealed : Fin n → Prop) [DecidablePred revealed],
    ∀ (hp : revealed participant)
      (hnu : nu ∈ stableFiber P base.1 revealed),
      rotation ∈ stableRotationIdeal P hstable
        (⟨nu, ((mem_stableFiber_iff P base.1 nu revealed).1 hnu).1⟩ :
          CodedStable P)

theorem exists_canonicalExtraLeftWitness {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m forbidden : Fin n)
    (hforbidden : forbidden ≠ m)
    (hextra : canonicalExtraLeft P hstable base m) :
    Nonempty (CanonicalExtraLeftWitness P hstable base m forbidden) := by
  classical
  rcases hextra.2 with ⟨r, hlast, hlarge | hnonmax⟩
  · have hrInfo := (mem_includedInvolvingRotations_iff
      P hstable base m r).1 hlast.1
    obtain ⟨p, hpMen, hpm, hpforbidden⟩ := exists_mem_ne_ne_of_three_le_card
      (canonicalRotationMen P hstable r) m forbidden hlarge
    have hpInv := (mem_canonicalRotationMen_iff P hstable r p).1 hpMen
    refine ⟨{
      rotation := r
      participant := p
      participant_ne := hpm
      participant_ne_forbidden := hpforbidden
      rotation_last := hlast
      rotation_mem_base := hrInfo.1
      rotation_involves_target := hrInfo.2
      forced_in_fiber := ?_ }⟩
    intro nu revealed _ hp hnu
    exact involved_rotation_forced_in_stableFiber
      P hstable base nu revealed p r hpInv hrInfo.1 hp hnu
  · have hrInfo := (mem_includedInvolvingRotations_iff
      P hstable base m r).1 hlast.1
    have hsExists : ∃ s : CanonicalRotation P,
        s ∈ stableRotationIdeal P hstable base ∧ r < s := by
      by_contra hnone
      apply hnonmax
      refine ⟨hrInfo.1, ?_⟩
      intro s hs hrs
      have hsrle : s ≤ r := by
        by_contra hsr
        have hrne : r ≠ s := fun he ↦ hsr he.symm.le
        have hrlt : r < s := lt_of_le_of_ne hrs hrne
        exact hnone ⟨s, hs, hrlt⟩
      exact (le_antisymm hrs hsrle).symm
    obtain ⟨s, hsBase, hrs⟩ := hsExists
    have hsNotInvM : ¬ canonicalRotationInvolvesMan P hstable m s := by
      intro hsInvM
      have hsIncluded : s ∈ includedInvolvingRotations P hstable base m :=
        (mem_includedInvolvingRotations_iff P hstable base m s).2
          ⟨hsBase, hsInvM⟩
      exact (not_lt_of_ge (hlast.2 s hsIncluded)) hrs
    have hsCard := two_le_card_canonicalRotationMen P hstable s
    obtain ⟨p, hpMen, hpforbidden⟩ := exists_mem_ne_of_two_le_card
      (canonicalRotationMen P hstable s) forbidden hsCard
    have hpm : p ≠ m := by
      intro hpm
      subst p
      exact hsNotInvM ((mem_canonicalRotationMen_iff P hstable s m).1 hpMen)
    have hpInv := (mem_canonicalRotationMen_iff P hstable s p).1 hpMen
    refine ⟨{
      rotation := r
      participant := p
      participant_ne := hpm
      participant_ne_forbidden := hpforbidden
      rotation_last := hlast
      rotation_mem_base := hrInfo.1
      rotation_involves_target := hrInfo.2
      forced_in_fiber := ?_ }⟩
    intro nu revealed _ hp hnu
    exact earlier_rotation_forced_in_stableFiber
      P hstable base nu revealed p r s hrs.le hpInv hsBase hp hnu

theorem canonicalRotationAfterIndex_strictAnti_of_lt_involving {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    {r s : CanonicalRotation P} (hrs : r < s)
    (hsInv : canonicalRotationInvolvesMan P hstable m s) :
    (canonicalRotationAfterIndex P hstable m E s).val <
      (canonicalRotationAfterIndex P hstable m E r).val := by
  have hle := rotationAfter_le_rotationBefore_of_lt_canonical
    P hstable hrs
  have hbeforeLe : P.manRank m ((rotationBefore P hstable s).1 m) ≤
      P.manRank m ((rotationAfter P hstable r).1 m) := hle m
  have hstrict := involved_manRank_strict P hstable m s hsInv
  have hrank : P.manRank m ((rotationAfter P hstable s).1 m) <
      P.manRank m ((rotationAfter P hstable r).1 m) :=
    hstrict.trans_le hbeforeLe
  rw [canonicalRotationAfterIndex_spec P hstable m E s,
    canonicalRotationAfterIndex_spec P hstable m E r] at hrank
  exact (E.ranked.rank_spec _ _).1 hrank

theorem lastIncludedInvolving_afterIndex_eq_center {n q : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (E : ExactStablePartnerEnumeration (q := q) P.toCore m)
    (j : Fin q) (hbase : base.1 m = E.ranked.partner j)
    (r : CanonicalRotation P)
    (hlast : IsLastIncludedInvolving P hstable base m r) :
    canonicalRotationAfterIndex P hstable m E r = j := by
  have hrInfo := (mem_includedInvolvingRotations_iff
    P hstable base m r).1 hlast.1
  have hjr := (mem_rotationIdeal_iff_center_le_afterIndex
    P hstable base m E j hbase r hrInfo.2).1 hrInfo.1
  have hrLast := canonicalRotationAfterIndex_lt_last
    P hstable m E r hrInfo.2
  have hjNext : j.val + 1 < q := by omega
  obtain ⟨s, hsInv, hsIndex⟩ :=
    exists_involving_rotation_with_afterIndex P hstable m E j hjNext
  have hsMem : s ∈ includedInvolvingRotations P hstable base m := by
    apply (mem_includedInvolvingRotations_iff P hstable base m s).2
    refine ⟨?_, hsInv⟩
    apply (mem_rotationIdeal_iff_center_le_afterIndex
      P hstable base m E j hbase s hsInv).2
    rw [hsIndex]
  have hsr := hlast.2 s hsMem
  rcases hsr.eq_or_lt with hsrEq | hsrLt
  · subst s
    exact hsIndex
  · have hanti := canonicalRotationAfterIndex_strictAnti_of_lt_involving
      P hstable m E hsrLt hrInfo.2
    rw [hsIndex] at hanti
    omega

end

end StableMatchingsJointCharging
