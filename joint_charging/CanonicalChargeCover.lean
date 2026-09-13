import «CanonicalDeletionFiber»
import Mathlib.Order.Preorder.Finite

/-!
# Canonical shallow/extra charge cover

The charge classes are expressed directly through the canonical rotation
chain of each man.  This avoids any unformalized indexing convention: a man
is shallow when at most one involving rotation lies on either side of the
ideal cut.  Otherwise, the last included involving rotation either has at
least three participants, is not globally maximal, or covers the man in the
maximal length-two frontier.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

def includedInvolvingRotations {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) :
    Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact Finset.univ.filter fun r ↦
    r ∈ stableRotationIdeal P hstable base ∧
      canonicalRotationInvolvesMan P hstable m r

def excludedInvolvingRotations {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) :
    Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact Finset.univ.filter fun r ↦
    r ∉ stableRotationIdeal P hstable base ∧
      canonicalRotationInvolvesMan P hstable m r

@[simp] theorem mem_includedInvolvingRotations_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) (r : CanonicalRotation P) :
    r ∈ includedInvolvingRotations P hstable base m ↔
      r ∈ stableRotationIdeal P hstable base ∧
        canonicalRotationInvolvesMan P hstable m r := by
  classical
  simp [includedInvolvingRotations]

@[simp] theorem mem_excludedInvolvingRotations_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) (r : CanonicalRotation P) :
    r ∈ excludedInvolvingRotations P hstable base m ↔
      r ∉ stableRotationIdeal P hstable base ∧
        canonicalRotationInvolvesMan P hstable m r := by
  classical
  simp [excludedInvolvingRotations]

def canonicalShallow {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) : Prop :=
  (includedInvolvingRotations P hstable base m).card ≤ 1 ∨
    (excludedInvolvingRotations P hstable base m).card ≤ 1

def IsLastIncludedInvolving {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (r : CanonicalRotation P) : Prop :=
  r ∈ includedInvolvingRotations P hstable base m ∧
    ∀ s ∈ includedInvolvingRotations P hstable base m, s ≤ r

def canonicalExtraLeft {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) : Prop :=
  ¬ canonicalShallow P hstable base m ∧
    ∃ r : CanonicalRotation P,
      IsLastIncludedInvolving P hstable base m r ∧
      (3 ≤ (canonicalRotationMen P hstable r).card ∨
        ¬ IsMaximalIn (stableRotationIdeal P hstable base) r)

theorem exists_lastIncludedInvolving_of_not_shallow {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (hdeep : ¬ canonicalShallow P hstable base m) :
    ∃ r : CanonicalRotation P,
      IsLastIncludedInvolving P hstable base m r := by
  classical
  let T := includedInvolvingRotations P hstable base m
  have hcard0 : 2 ≤
      (includedInvolvingRotations P hstable base m).card := by
    simp only [canonicalShallow, not_or] at hdeep
    omega
  have hcard : 2 ≤ T.card := by simpa [T] using hcard0
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hrmax⟩ := T.exists_maximal hT
  refine ⟨r, hrmax.1, ?_⟩
  intro s hs
  rcases canonicalRotations_involving_man_comparable P hstable m
      ((mem_includedInvolvingRotations_iff P hstable base m s).1 hs).2
      ((mem_includedInvolvingRotations_iff P hstable base m r).1 hrmax.1).2 with
    hsr | hrs
  · exact hsr
  · exact hrmax.2 hs hrs

theorem uncovered_man_is_shallow_or_extra {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n)
    (huncovered : m ∉ canonicalRotationSupport P hstable
      (maximalLengthTwoFrontier P hstable base)) :
    canonicalShallow P hstable base m ∨
      canonicalExtraLeft P hstable base m := by
  classical
  by_cases hshallow : canonicalShallow P hstable base m
  · exact Or.inl hshallow
  · right
    refine ⟨hshallow, ?_⟩
    obtain ⟨r, hlast⟩ :=
      exists_lastIncludedInvolving_of_not_shallow P hstable base m hshallow
    refine ⟨r, hlast, ?_⟩
    by_cases hmax : IsMaximalIn (stableRotationIdeal P hstable base) r
    · left
      have htwoNot : ¬ canonicalLengthTwo P hstable r := by
        intro htwo
        apply huncovered
        exact ⟨r,
          (mem_maximalLengthTwoFrontier_iff P hstable base r).2
            ⟨hmax, htwo⟩,
          (mem_canonicalRotationMen_iff P hstable r m).2
            ((mem_includedInvolvingRotations_iff
              P hstable base m r).1 hlast.1).2⟩
      have htwoLe := two_le_card_canonicalRotationMen P hstable r
      simp only [canonicalLengthTwo] at htwoNot
      omega
    · exact Or.inr hmax

def canonicalChargedMen {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun m ↦
    canonicalShallow P hstable base m ∨
      canonicalExtraLeft P hstable base m

@[simp] theorem mem_canonicalChargedMen_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) :
    m ∈ canonicalChargedMen P hstable base ↔
      canonicalShallow P hstable base m ∨
        canonicalExtraLeft P hstable base m := by
  classical
  simp [canonicalChargedMen]

theorem canonicalUncoveredMen_subset_chargedMen {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base image : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable base)
    (himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable base \ A) :
    canonicalUncoveredMen
        ({ source := base, deleted := A,
           deleted_subset := hA, image_ideal_eq := himage } :
          CanonicalDeletionFiber P hstable image) ⊆
      canonicalChargedMen P hstable base := by
  classical
  intro m hm
  have hmUncovered : m ∉ canonicalRotationSupport P hstable
      (maximalLengthTwoFrontier P hstable base) := by
    simpa [canonicalUncoveredMen, canonicalDeletionSourceFrontier] using hm
  exact (mem_canonicalChargedMen_iff P hstable base m).2
    (uncovered_man_is_shallow_or_extra P hstable base m hmUncovered)

theorem card_canonicalUncoveredMen_le_card_chargedMen {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base image : CodedStable P) (A : Finset (CanonicalRotation P))
    (hA : A ⊆ maximalLengthTwoFrontier P hstable base)
    (himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable base \ A) :
    (canonicalUncoveredMen
        ({ source := base, deleted := A,
           deleted_subset := hA, image_ideal_eq := himage } :
          CanonicalDeletionFiber P hstable image)).card ≤
      (canonicalChargedMen P hstable base).card :=
  Finset.card_le_card
    (canonicalUncoveredMen_subset_chargedMen
      P hstable base image A hA himage)

def CanonicalDeletionFiberWithSourceChargeAtMost {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :=
  {D : CanonicalDeletionFiber P hstable image //
    (canonicalChargedMen P hstable D.source).card ≤ k}

noncomputable def sourceChargeFiberToUncoveredFiber {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {k : Nat}
    (D : CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k) :
    CanonicalDeletionFiberWithUncoveredAtMost P hstable image k :=
  ⟨D.1, (card_canonicalUncoveredMen_le_card_chargedMen
      P hstable D.1.source image D.1.deleted
        D.1.deleted_subset D.1.image_ideal_eq).trans D.2⟩

theorem sourceChargeFiberToUncoveredFiber_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {k : Nat} :
    Function.Injective
      (sourceChargeFiberToUncoveredFiber
        (P := P) (hstable := hstable) (image := image) (k := k)) := by
  intro D E h
  apply Subtype.ext
  exact congrArg (fun z : CanonicalDeletionFiberWithUncoveredAtMost
    P hstable image k ↦ z.1) h

noncomputable instance canonicalDeletionFiberWithSourceChargeAtMostFinite
    {n : Nat} (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Finite (CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k) :=
  Finite.of_injective
    (sourceChargeFiberToUncoveredFiber
      (P := P) (hstable := hstable) (image := image) (k := k))
    (sourceChargeFiberToUncoveredFiber_injective
      (P := P) (hstable := hstable) (image := image) (k := k))

theorem natCard_sourceChargeDeletionFiber_le {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Nat.card (CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k) ≤
      2 ^ (n / 4) *
        (∑ i ∈ Finset.range (k + 1), n.choose i) := by
  letI (U : AdmissibleMissingSet n k) :
      Finite (CanonicalBoundaryMatchingData P hstable image
        (canonicalCoveredSetFromMissing U.1)) :=
    Finite.of_injective
      (canonicalBoundaryMatchingEncode
        (P := P) (hstable := hstable) (base := image)
          (S := canonicalCoveredSetFromMissing U.1))
      (canonicalBoundaryMatchingEncode_injective
        (P := P) (hstable := hstable) (base := image)
          (S := canonicalCoveredSetFromMissing U.1))
  letI (U : AdmissibleMissingSet n k) :
      Finite (CanonicalDeletionFiberAtSupport P hstable image
        (canonicalCoveredSetFromMissing U.1)) :=
    Finite.of_injective
      (canonicalDeletionFiberAtSupportEncode
        (P := P) (hstable := hstable) (image := image)
          (S := canonicalCoveredSetFromMissing U.1))
      (canonicalDeletionFiberAtSupportEncode_injective
        (P := P) (hstable := hstable) (image := image)
          (S := canonicalCoveredSetFromMissing U.1))
  letI : Finite (CanonicalDeletionFiberSupportCode P hstable image k) := by
    dsimp [CanonicalDeletionFiberSupportCode]
    infer_instance
  letI : Finite (CanonicalDeletionFiberWithUncoveredAtMost
      P hstable image k) :=
    Finite.of_injective
      (canonicalDeletionFiberSupportEncode
        (P := P) (hstable := hstable) (image := image) (k := k))
      (canonicalDeletionFiberSupportEncode_injective
        (P := P) (hstable := hstable) (image := image) (k := k))
  letI : Finite (CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k) :=
    Finite.of_injective
      (sourceChargeFiberToUncoveredFiber
        (P := P) (hstable := hstable) (image := image) (k := k))
      (sourceChargeFiberToUncoveredFiber_injective
        (P := P) (hstable := hstable) (image := image) (k := k))
  exact (Nat.card_le_card_of_injective
    (sourceChargeFiberToUncoveredFiber
      (P := P) (hstable := hstable) (image := image) (k := k))
    (sourceChargeFiberToUncoveredFiber_injective
      (P := P) (hstable := hstable) (image := image) (k := k))).trans
    (natCard_canonicalDeletionFiberWithUncoveredAtMost_le
      P hstable image k)

def canonicalFrontierCoveredMen {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) : Finset (Fin n) := by
  classical
  exact (maximalLengthTwoFrontier P hstable base).biUnion fun r ↦
    canonicalRotationMen P hstable r

@[simp] theorem mem_canonicalFrontierCoveredMen_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (m : Fin n) :
    m ∈ canonicalFrontierCoveredMen P hstable base ↔
      m ∈ canonicalRotationSupport P hstable
        (maximalLengthTwoFrontier P hstable base) := by
  classical
  simp [canonicalFrontierCoveredMen, canonicalRotationSupport]

theorem card_canonicalFrontierCoveredMen {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    (canonicalFrontierCoveredMen P hstable base).card =
      2 * (maximalLengthTwoFrontier P hstable base).card := by
  classical
  rw [canonicalFrontierCoveredMen, Finset.card_biUnion]
  · calc
      (∑ r ∈ maximalLengthTwoFrontier P hstable base,
          (canonicalRotationMen P hstable r).card) =
          ∑ _r ∈ maximalLengthTwoFrontier P hstable base, 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        exact ((mem_maximalLengthTwoFrontier_iff
          P hstable base r).1 hr).2
      _ = 2 * (maximalLengthTwoFrontier P hstable base).card := by
        simp [Nat.mul_comm]
  · intro r hr s hs hrs
    exact canonicalRotationMen_disjoint_of_distinct_maximal
      P hstable base
      ((mem_maximalLengthTwoFrontier_iff P hstable base r).1 hr).1
      ((mem_maximalLengthTwoFrontier_iff P hstable base s).1 hs).1 hrs

theorem frontier_card_lower_of_charge_card_le {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (k : Nat)
    (hcharge : (canonicalChargedMen P hstable base).card ≤ k) :
    (n - k) / 2 ≤
      (maximalLengthTwoFrontier P hstable base).card := by
  classical
  have huncovered : ((Finset.univ : Finset (Fin n)) \
      canonicalFrontierCoveredMen P hstable base).card ≤ k := by
    apply (Finset.card_le_card ?_).trans hcharge
    intro m hm
    have hmNotCovered : m ∉ canonicalRotationSupport P hstable
        (maximalLengthTwoFrontier P hstable base) := by
      intro hmCovered
      exact (Finset.mem_sdiff.mp hm).2
        ((mem_canonicalFrontierCoveredMen_iff
        P hstable base m).2 hmCovered)
    exact (mem_canonicalChargedMen_iff P hstable base m).2
      (uncovered_man_is_shallow_or_extra
        P hstable base m hmNotCovered)
  have hcovered : n - k ≤
      (canonicalFrontierCoveredMen P hstable base).card := by
    have hsubset : canonicalFrontierCoveredMen P hstable base ⊆
        (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
    rw [Finset.card_sdiff_of_subset hsubset, Finset.card_univ,
      Fintype.card_fin] at huncovered
    omega
  rw [card_canonicalFrontierCoveredMen P hstable base] at hcovered
  omega

end

end StableMatchingsJointCharging
