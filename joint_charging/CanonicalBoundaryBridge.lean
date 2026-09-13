import «CanonicalRotationChain»

/-!
# Canonical boundary rotations for an actual stable-marriage profile

This module instantiates the abstract deletion-frontier lemmas with the
Birkhoff rotations constructed from `ProfileCode`.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

def canonicalLengthTwo {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) : Prop :=
  (canonicalRotationMen P hstable r).card = 2

def maximalLengthTwoFrontier {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) :
    Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact Finset.univ.filter fun r ↦
    IsMaximalIn (stableRotationIdeal P hstable base) r ∧
      canonicalLengthTwo P hstable r

@[simp] theorem mem_maximalLengthTwoFrontier_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (r : CanonicalRotation P) :
    r ∈ maximalLengthTwoFrontier P hstable base ↔
      IsMaximalIn (stableRotationIdeal P hstable base) r ∧
        canonicalLengthTwo P hstable r := by
  classical
  simp [maximalLengthTwoFrontier]

def minimalLengthTwoOutsideFrontier {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) :
    Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact Finset.univ.filter fun r ↦
    IsMinimalOutside (stableRotationIdeal P hstable base) r ∧
      canonicalLengthTwo P hstable r

@[simp] theorem mem_minimalLengthTwoOutsideFrontier_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (r : CanonicalRotation P) :
    r ∈ minimalLengthTwoOutsideFrontier P hstable base ↔
      IsMinimalOutside (stableRotationIdeal P hstable base) r ∧
        canonicalLengthTwo P hstable r := by
  classical
  simp [minimalLengthTwoOutsideFrontier]

def canonicalBoundaryLengthTwoFrontier {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) :
    Finset (CanonicalRotation P) :=
  maximalLengthTwoFrontier P hstable base ∪
    minimalLengthTwoOutsideFrontier P hstable base

@[simp] theorem mem_canonicalBoundaryLengthTwoFrontier_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (r : CanonicalRotation P) :
    r ∈ canonicalBoundaryLengthTwoFrontier P hstable base ↔
      (IsMaximalIn (stableRotationIdeal P hstable base) r ∧
        canonicalLengthTwo P hstable r) ∨
      (IsMinimalOutside (stableRotationIdeal P hstable base) r ∧
        canonicalLengthTwo P hstable r) := by
  classical
  simp [canonicalBoundaryLengthTwoFrontier]

theorem canonical_maximal_involving_unique {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) {r s : CanonicalRotation P}
    (hrm : canonicalRotationInvolvesMan P hstable m r)
    (hsm : canonicalRotationInvolvesMan P hstable m s)
    (hr : IsMaximalIn (stableRotationIdeal P hstable base) r)
    (hs : IsMaximalIn (stableRotationIdeal P hstable base) s) :
    r = s := by
  exact maximal_in_participant_chain_unique
    (canonicalRotationInvolvesMan P hstable m)
    (fun _ _ ↦ canonicalRotations_involving_man_comparable P hstable m)
    hrm hsm hr hs

theorem canonical_minimal_outside_involving_unique {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) {r s : CanonicalRotation P}
    (hrm : canonicalRotationInvolvesMan P hstable m r)
    (hsm : canonicalRotationInvolvesMan P hstable m s)
    (hr : IsMinimalOutside (stableRotationIdeal P hstable base) r)
    (hs : IsMinimalOutside (stableRotationIdeal P hstable base) s) :
    r = s := by
  exact minimal_outside_participant_chain_unique
    (canonicalRotationInvolvesMan P hstable m)
    (fun _ _ ↦ canonicalRotations_involving_man_comparable P hstable m)
    hrm hsm hr hs

theorem canonical_boundary_pair_is_cover {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) {r s : CanonicalRotation P}
    (hrm : canonicalRotationInvolvesMan P hstable m r)
    (hsm : canonicalRotationInvolvesMan P hstable m s)
    (hr : IsMaximalIn (stableRotationIdeal P hstable base) r)
    (hs : IsMinimalOutside (stableRotationIdeal P hstable base) s) :
    r < s ∧ ¬ ∃ t : CanonicalRotation P, r < t ∧ t < s := by
  exact participant_boundary_is_cover
    (canonicalRotationInvolvesMan P hstable m)
    (fun _ _ ↦ canonicalRotations_involving_man_comparable P hstable m)
    hrm hsm (stableRotationIdeal_isIdeal P hstable base) hr hs

theorem canonicalRotationMen_disjoint_of_distinct_maximal {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) {r s : CanonicalRotation P}
    (hr : IsMaximalIn (stableRotationIdeal P hstable base) r)
    (hs : IsMaximalIn (stableRotationIdeal P hstable base) s)
    (hne : r ≠ s) :
    Disjoint (canonicalRotationMen P hstable r)
      (canonicalRotationMen P hstable s) := by
  rw [Finset.disjoint_left]
  intro m hmr hms
  have hrm := (mem_canonicalRotationMen_iff P hstable r m).1 hmr
  have hsm := (mem_canonicalRotationMen_iff P hstable s m).1 hms
  exact hne (canonical_maximal_involving_unique P hstable base m hrm hsm hr hs)

theorem canonicalRotationMen_disjoint_of_distinct_minimalOutside {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) {r s : CanonicalRotation P}
    (hr : IsMinimalOutside (stableRotationIdeal P hstable base) r)
    (hs : IsMinimalOutside (stableRotationIdeal P hstable base) s)
    (hne : r ≠ s) :
    Disjoint (canonicalRotationMen P hstable r)
      (canonicalRotationMen P hstable s) := by
  rw [Finset.disjoint_left]
  intro m hmr hms
  have hrm := (mem_canonicalRotationMen_iff P hstable r m).1 hmr
  have hsm := (mem_canonicalRotationMen_iff P hstable s m).1 hms
  exact hne
    (canonical_minimal_outside_involving_unique P hstable base m hrm hsm hr hs)

theorem rotationAfter_le_rotationBefore_of_lt {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    {r s : CanonicalRotation P} (hrs : r < s) :
    rotationAfter P hstable r ≤ rotationBefore P hstable s := by
  let e := stableBirkhoffLowerSet P hstable
  apply e.symm.monotone
  intro t ht
  change t ≤ r at ht
  change t < s
  exact ht.trans_lt hrs

/-- No participant of the lower boundary rotation can change partner in the
context interval between two consecutive canonical rotations. -/
theorem boundary_gap_preserves_man_partner {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n) {r s : CanonicalRotation P}
    (hrm : canonicalRotationInvolvesMan P hstable m r)
    (hrs : r < s) (hgap : ¬ ∃ t : CanonicalRotation P, r < t ∧ t < s) :
    (rotationAfter P hstable r).1 m =
      (rotationBefore P hstable s).1 m := by
  apply man_partner_eq_of_no_involving_rotation_in_ideal_diff
    P hstable (rotationAfter P hstable r) (rotationBefore P hstable s) m
    (rotationAfter_le_rotationBefore_of_lt P hstable hrs)
  intro t hts hntr htm
  have hts' : t < s :=
    (mem_rotationIdeal_rotationBefore_iff P hstable s t).1 hts
  have hntr' : ¬ t ≤ r := by
    intro htr
    exact hntr ((mem_rotationIdeal_rotationAfter_iff P hstable r t).2 htr)
  have hcomp := canonicalRotations_involving_man_comparable
    P hstable m htm hrm
  have hrt : r < t := by
    rcases hcomp with htr | hrt
    · exact False.elim (hntr' htr)
    · exact lt_of_le_of_ne hrt (fun h ↦ hntr' h.symm.le)
  exact False.elim (hgap ⟨t, hrt, hts'⟩)

/-- If two permutations differ exactly on a pair of coordinates, the two
images are exchanged. -/
theorem equiv_swap_of_diff_eq_pair {n : Nat}
    (f g : Equiv.Perm (Fin n)) (m p : Fin n) (hmp : m ≠ p)
    (hdiff : ∀ x, f x ≠ g x ↔ x ∈ ({m, p} : Finset (Fin n))) :
    f m = g p ∧ f p = g m := by
  have first : ∀ a b : Fin n, a ≠ b → f a ≠ g a →
      (∀ x, x ≠ a → x ≠ b → f x = g x) → f a = g b := by
    intro a b hab ha hout
    let q := g.symm (f a)
    have hgq : g q = f a := g.apply_symm_apply (f a)
    have hqa : q ≠ a := by
      intro h
      exact ha (hgq.symm.trans (congrArg g h))
    have hqb : q = b := by
      by_contra hqb
      have hfg := hout q hqa hqb
      have hfa : f q = f a := hfg.trans hgq
      exact hqa (f.injective hfa)
    rw [← hqb]
    exact hgq.symm
  have hm : f m ≠ g m := (hdiff m).2 (by simp)
  have hp : f p ≠ g p := (hdiff p).2 (by simp)
  have houtMP : ∀ x, x ≠ m → x ≠ p → f x = g x := by
    intro x hxm hxp
    exact not_ne_iff.mp ((hdiff x).not.mpr (by simp [hxm, hxp]))
  have houtPM : ∀ x, x ≠ p → x ≠ m → f x = g x := by
    intro x hxp hxm
    exact houtMP x hxm hxp
  exact ⟨first m p hmp hm houtMP, first p m hmp.symm hp houtPM⟩

theorem canonicalRotation_swaps_two_men {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (r : CanonicalRotation P) (m p : Fin n) (hmp : m ≠ p)
    (hm : m ∈ canonicalRotationMen P hstable r)
    (hp : p ∈ canonicalRotationMen P hstable r)
    (hlen : canonicalLengthTwo P hstable r) :
    (rotationBefore P hstable r).1 m = (rotationAfter P hstable r).1 p ∧
      (rotationBefore P hstable r).1 p = (rotationAfter P hstable r).1 m := by
  have hsub : ({m, p} : Finset (Fin n)) ⊆
      canonicalRotationMen P hstable r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hm
    · exact hp
  have hcard : (canonicalRotationMen P hstable r).card ≤
      ({m, p} : Finset (Fin n)).card := by
    simp [canonicalLengthTwo] at hlen
    simp [hlen, hmp]
  have heq : ({m, p} : Finset (Fin n)) =
      canonicalRotationMen P hstable r :=
    Finset.eq_of_subset_of_card_le hsub hcard
  apply equiv_swap_of_diff_eq_pair
    (rotationBefore P hstable r).1 (rotationAfter P hstable r).1 m p hmp
  intro x
  simpa [canonicalRotationInvolvesMan, heq] using
    (mem_canonicalRotationMen_iff P hstable r x).symm

/-- The in-frontier and out-frontier two-person rotations cannot be parallel
edges on the same unordered pair of men.  Together with same-color
disjointness this is the exact graph-theoretic input for the alternating
path/even-cycle boundary encoding. -/
theorem canonical_boundary_lengthTwo_no_parallel {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) {r s : CanonicalRotation P}
    (hr : IsMaximalIn (stableRotationIdeal P hstable base) r)
    (hs : IsMinimalOutside (stableRotationIdeal P hstable base) s)
    (hlenr : canonicalLengthTwo P hstable r)
    (hlens : canonicalLengthTwo P hstable s) :
    canonicalRotationMen P hstable r ≠
      canonicalRotationMen P hstable s := by
  intro heq
  obtain ⟨m, p, hmp, hrpair⟩ :=
    Finset.card_eq_two.mp hlenr
  have hspair : canonicalRotationMen P hstable s = ({m, p} : Finset (Fin n)) :=
    heq.symm.trans hrpair
  have hmr : m ∈ canonicalRotationMen P hstable r := by simp [hrpair]
  have hpr : p ∈ canonicalRotationMen P hstable r := by simp [hrpair]
  have hms : m ∈ canonicalRotationMen P hstable s := by simp [hspair]
  have hps : p ∈ canonicalRotationMen P hstable s := by simp [hspair]
  have hmri := (mem_canonicalRotationMen_iff P hstable r m).1 hmr
  have hmsi := (mem_canonicalRotationMen_iff P hstable s m).1 hms
  obtain ⟨hrs, hgap⟩ := canonical_boundary_pair_is_cover
    P hstable base m hmri hmsi hr hs
  have hgapm := boundary_gap_preserves_man_partner
    P hstable m hmri hrs hgap
  have hpri := (mem_canonicalRotationMen_iff P hstable r p).1 hpr
  have hgapp := boundary_gap_preserves_man_partner
    P hstable p hpri hrs hgap
  have rswap := canonicalRotation_swaps_two_men
    P hstable r m p hmp hmr hpr hlenr
  have sswap := canonicalRotation_swaps_two_men
    P hstable s m p hmp hms hps hlens
  have hafterM : (rotationAfter P hstable s).1 m =
      (rotationBefore P hstable r).1 m :=
    sswap.2.symm.trans (hgapp.symm.trans rswap.1.symm)
  have hrstrict := involved_manRank_strict P hstable m r hmri
  have hsstrict := involved_manRank_strict P hstable m s hmsi
  rw [hafterM, ← hgapm] at hsstrict
  omega

theorem canonicalBoundaryRotation_support_injective {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    Function.Injective (fun r :
      {r : CanonicalRotation P //
        r ∈ canonicalBoundaryLengthTwoFrontier P hstable base} ↦
      canonicalRotationMen P hstable r.1) := by
  classical
  intro r s hsupport
  apply Subtype.ext
  have hrInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
    P hstable base r.1).1 r.2
  have hsInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
    P hstable base s.1).1 s.2
  have hrCard : (canonicalRotationMen P hstable r.1).card = 2 := by
    rcases hrInfo with hr | hr <;> exact hr.2
  have hrNonempty : (canonicalRotationMen P hstable r.1).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨m, hmr⟩ := hrNonempty
  have hsupport' : canonicalRotationMen P hstable r.1 =
      canonicalRotationMen P hstable s.1 := hsupport
  have hms : m ∈ canonicalRotationMen P hstable s.1 := by
    exact hsupport' ▸ hmr
  have hrm := (mem_canonicalRotationMen_iff P hstable r.1 m).1 hmr
  have hsm := (mem_canonicalRotationMen_iff P hstable s.1 m).1 hms
  rcases hrInfo with hrMax | hrMin
  · rcases hsInfo with hsMax | hsMin
    · exact canonical_maximal_involving_unique
        P hstable base m hrm hsm hrMax.1 hsMax.1
    · exact False.elim
        ((canonical_boundary_lengthTwo_no_parallel P hstable base
          hrMax.1 hsMin.1 hrMax.2 hsMin.2) hsupport')
  · rcases hsInfo with hsMax | hsMin
    · exact False.elim
        ((canonical_boundary_lengthTwo_no_parallel P hstable base
          hsMax.1 hrMin.1 hsMax.2 hrMin.2) hsupport'.symm)
    · exact canonical_minimal_outside_involving_unique
        P hstable base m hrm hsm hrMin.1 hsMin.1

theorem maximalIn_sdiff_of_maximalIn_not_mem
    {R : Type*} [PartialOrder R] [DecidableEq R]
    {D A : Finset R} {r : R} (hr : IsMaximalIn D r) (hrA : r ∉ A) :
    IsMaximalIn (D \ A) r := by
  refine ⟨Finset.mem_sdiff.mpr ⟨hr.1, hrA⟩, ?_⟩
  intro s hs hrs
  exact hr.2 (Finset.mem_sdiff.mp hs).1 hrs

/-- Exact profile-level deletion bridge.  Deleting any subset of the
length-two maximal frontier produces another actual stable matching, and the
entire old frontier embeds in the two-colored boundary frontier of the image.
The removed subset and original ideal are recovered without loss. -/
theorem canonical_frontier_deletion_realized_and_recoverable {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable base) :
    ∃ image : CodedStable P,
      stableRotationIdeal P hstable image =
          stableRotationIdeal P hstable base \ A ∧
      maximalLengthTwoFrontier P hstable base ⊆
          canonicalBoundaryLengthTwoFrontier P hstable image ∧
      maximalLengthTwoFrontier P hstable base \
          stableRotationIdeal P hstable image = A ∧
      stableRotationIdeal P hstable image ∪ A =
          stableRotationIdeal P hstable base := by
  classical
  let D := stableRotationIdeal P hstable base
  let L := maximalLengthTwoFrontier P hstable base
  have hD : IsFinsetIdeal D := stableRotationIdeal_isIdeal P hstable base
  have hAD : A ⊆ D := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable base r).1 (hA hrA)).1.1
  have hmaxA : ∀ r ∈ A, IsMaximalIn D r := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable base r).1 (hA hrA)).1
  have hJ : IsFinsetIdeal (D \ A) :=
    ideal_sdiff_maximal_subset D A hD hAD hmaxA
  let image := codedStableOfIdeal P hstable (D \ A) hJ
  have himage : stableRotationIdeal P hstable image = D \ A :=
    stableRotationIdeal_codedStableOfIdeal_eq P hstable (D \ A) hJ
  refine ⟨image, himage, ?_, ?_, ?_⟩
  · intro r hrL
    have hrInfo := (mem_maximalLengthTwoFrontier_iff P hstable base r).1 hrL
    rw [mem_canonicalBoundaryLengthTwoFrontier_iff]
    by_cases hrA : r ∈ A
    · right
      refine ⟨?_, hrInfo.2⟩
      rw [himage]
      exact removed_maximal_is_minimal_outside D A hD hAD hmaxA hrA
    · left
      refine ⟨?_, hrInfo.2⟩
      rw [himage]
      exact maximalIn_sdiff_of_maximalIn_not_mem hrInfo.1 hrA
  · rw [himage]
    exact recover_deleted_subset D L A hA (by
      intro r hrL
      exact ((mem_maximalLengthTwoFrontier_iff P hstable base r).1 hrL).1.1)
  · rw [himage]
    exact recover_deleted_ideal D A hAD

/-- Any stable matching whose rotation ideal is obtained by deleting a subset
of the source maximal length-two frontier has the entire old frontier in its
two-colored boundary.  This formulation is used for arbitrary members of a
fixed-image deletion fiber. -/
theorem canonical_frontier_subset_boundary_of_ideal_eq_sdiff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (source image : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable source)
    (himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable source \ A) :
    maximalLengthTwoFrontier P hstable source ⊆
      canonicalBoundaryLengthTwoFrontier P hstable image := by
  classical
  let D := stableRotationIdeal P hstable source
  have hD : IsFinsetIdeal D := stableRotationIdeal_isIdeal P hstable source
  have hAD : A ⊆ D := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable source r).1
      (hA hrA)).1.1
  have hmaxA : ∀ r ∈ A, IsMaximalIn D r := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable source r).1
      (hA hrA)).1
  intro r hrL
  have hrInfo :=
    (mem_maximalLengthTwoFrontier_iff P hstable source r).1 hrL
  rw [mem_canonicalBoundaryLengthTwoFrontier_iff]
  by_cases hrA : r ∈ A
  · right
    refine ⟨?_, hrInfo.2⟩
    rw [himage]
    exact removed_maximal_is_minimal_outside D A hD hAD hmaxA hrA
  · left
    refine ⟨?_, hrInfo.2⟩
    rw [himage]
    exact maximalIn_sdiff_of_maximalIn_not_mem hrInfo.1 hrA

theorem canonical_deleted_subset_recovered_of_ideal_eq_sdiff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (source image : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable source)
    (himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable source \ A) :
    maximalLengthTwoFrontier P hstable source \
        stableRotationIdeal P hstable image = A := by
  rw [himage]
  exact recover_deleted_subset
    (stableRotationIdeal P hstable source)
    (maximalLengthTwoFrontier P hstable source) A hA (by
      intro r hrL
      exact ((mem_maximalLengthTwoFrontier_iff P hstable source r).1
        hrL).1.1)

theorem canonical_source_ideal_recovered_of_ideal_eq_sdiff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (source image : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable source)
    (himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable source \ A) :
    stableRotationIdeal P hstable image ∪ A =
      stableRotationIdeal P hstable source := by
  rw [himage]
  exact recover_deleted_ideal
    (stableRotationIdeal P hstable source) A (by
      intro r hrA
      exact ((mem_maximalLengthTwoFrontier_iff P hstable source r).1
        (hA hrA)).1.1)

end

end StableMatchingsJointCharging
