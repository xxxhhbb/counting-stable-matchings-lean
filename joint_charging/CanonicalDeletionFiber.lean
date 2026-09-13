import «CanonicalBoundaryMatchingEncoding»

/-!
# Actual fixed-image deletion fibers

This file packages the source stable matching and the deleted subset of its
maximal length-two rotation frontier.  For a fixed image, the full source
frontier recovers both fields, and for a fixed covered participant set it is
encoded by an actual perfect matching of the canonical boundary graph.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

@[ext] structure CanonicalDeletionFiber {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) where
  source : CodedStable P
  deleted : Finset (CanonicalRotation P)
  deleted_subset : deleted ⊆
    maximalLengthTwoFrontier P hstable source
  image_ideal_eq : stableRotationIdeal P hstable image =
    stableRotationIdeal P hstable source \ deleted

def canonicalDeletionSourceFrontier {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    Finset (CanonicalRotation P) :=
  maximalLengthTwoFrontier P hstable D.source

theorem canonicalDeletionSourceFrontier_subset_boundary {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    canonicalDeletionSourceFrontier D ⊆
      canonicalBoundaryLengthTwoFrontier P hstable image := by
  exact canonical_frontier_subset_boundary_of_ideal_eq_sdiff
    P hstable D.source image D.deleted D.deleted_subset D.image_ideal_eq

theorem canonicalDeletionFiber_deleted_recovered {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    canonicalDeletionSourceFrontier D \
        stableRotationIdeal P hstable image = D.deleted := by
  exact canonical_deleted_subset_recovered_of_ideal_eq_sdiff
    P hstable D.source image D.deleted D.deleted_subset D.image_ideal_eq

theorem canonicalDeletionFiber_source_ideal_recovered {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    stableRotationIdeal P hstable image ∪ D.deleted =
      stableRotationIdeal P hstable D.source := by
  exact canonical_source_ideal_recovered_of_ideal_eq_sdiff
    P hstable D.source image D.deleted D.deleted_subset D.image_ideal_eq

theorem canonicalDeletionSourceFrontier_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} :
    Function.Injective
      (canonicalDeletionSourceFrontier
        (P := P) (hstable := hstable) (image := image)) := by
  classical
  intro D E hfrontier
  have hdeleted : D.deleted = E.deleted := by
    rw [← canonicalDeletionFiber_deleted_recovered D,
      ← canonicalDeletionFiber_deleted_recovered E, hfrontier]
  have hideal : stableRotationIdeal P hstable D.source =
      stableRotationIdeal P hstable E.source := by
    rw [← canonicalDeletionFiber_source_ideal_recovered D,
      ← canonicalDeletionFiber_source_ideal_recovered E, hdeleted]
  have hsource : D.source = E.source :=
    stableRotationIdeal_injective P hstable hideal
  apply CanonicalDeletionFiber.ext
  · exact hsource
  · exact hdeleted

def CanonicalDeletionFiberAtSupport {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (S : Set (Fin n)) :=
  {D : CanonicalDeletionFiber P hstable image //
    canonicalRotationSupport P hstable
      (canonicalDeletionSourceFrontier D) = S}

noncomputable def canonicalDeletionFiberAtSupportEncode {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalDeletionFiberAtSupport P hstable image S) :
    CanonicalBoundaryMatchingData P hstable image S := by
  rcases D with ⟨D, hsupport⟩
  change canonicalRotationSupport P hstable
    (maximalLengthTwoFrontier P hstable D.source) = S at hsupport
  subst S
  exact maximalFrontierBoundaryMatchingData P hstable
    D.source image (canonicalDeletionSourceFrontier_subset_boundary D)

@[simp] theorem canonicalDeletionFiberAtSupportEncode_rotations {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalDeletionFiberAtSupport P hstable image S) :
    (canonicalDeletionFiberAtSupportEncode D).rotations =
      canonicalDeletionSourceFrontier D.1 := by
  rcases D with ⟨D, hsupport⟩
  change canonicalRotationSupport P hstable
    (maximalLengthTwoFrontier P hstable D.source) = S at hsupport
  subst S
  rfl

theorem canonicalDeletionFiberAtSupportEncode_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {S : Set (Fin n)} :
    Function.Injective
      (canonicalDeletionFiberAtSupportEncode
        (P := P) (hstable := hstable) (image := image) (S := S)) := by
  classical
  intro D E hcode
  apply Subtype.ext
  apply canonicalDeletionSourceFrontier_injective
  have hrot := congrArg CanonicalBoundaryMatchingData.rotations hcode
  simpa using hrot

noncomputable instance canonicalDeletionFiberAtSupportFinite {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (S : Set (Fin n)) :
    Finite (CanonicalDeletionFiberAtSupport P hstable image S) :=
  Finite.of_injective
    (canonicalDeletionFiberAtSupportEncode
      (P := P) (hstable := hstable) (image := image) (S := S))
    (canonicalDeletionFiberAtSupportEncode_injective
      (P := P) (hstable := hstable) (image := image) (S := S))

theorem natCard_canonicalDeletionFiberAtSupport_le_two_pow_quarter {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (S : Set (Fin n)) :
    Nat.card (CanonicalDeletionFiberAtSupport P hstable image S) ≤
      2 ^ (n / 4) := by
  letI : Finite (CanonicalBoundaryMatchingData P hstable image S) :=
    Finite.of_injective
      (canonicalBoundaryMatchingEncode
        (P := P) (hstable := hstable) (base := image) (S := S))
      (canonicalBoundaryMatchingEncode_injective
        (P := P) (hstable := hstable) (base := image) (S := S))
  letI : Finite (CanonicalDeletionFiberAtSupport P hstable image S) :=
    Finite.of_injective
      (canonicalDeletionFiberAtSupportEncode
        (P := P) (hstable := hstable) (image := image) (S := S))
      (canonicalDeletionFiberAtSupportEncode_injective
        (P := P) (hstable := hstable) (image := image) (S := S))
  have hencode := Nat.card_le_card_of_injective
    (canonicalDeletionFiberAtSupportEncode
      (P := P) (hstable := hstable) (image := image) (S := S))
    (canonicalDeletionFiberAtSupportEncode_injective
      (P := P) (hstable := hstable) (image := image) (S := S))
  exact hencode.trans
    (natCard_canonicalBoundaryMatchingData_le_two_pow_quarter
      P hstable image S)

/-! ## Summing over a bounded uncovered set -/

def admissibleMissingSets (n k : Nat) : Finset (Finset (Fin n)) :=
  (Finset.range (k + 1)).biUnion fun i ↦
    (Finset.univ : Finset (Fin n)).powersetCard i

@[simp] theorem mem_admissibleMissingSets_iff {n k : Nat}
    (U : Finset (Fin n)) :
    U ∈ admissibleMissingSets n k ↔ U.card ≤ k := by
  classical
  rw [admissibleMissingSets, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hU⟩
    have hiLe : i ≤ k := by simpa using hi
    exact ((Finset.mem_powersetCard.mp hU).2 ▸ hiLe)
  · intro hUk
    refine ⟨U.card, by simpa, ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U, rfl⟩

theorem card_admissibleMissingSets_le_binomialPrefix (n k : Nat) :
    (admissibleMissingSets n k).card ≤
      ∑ i ∈ Finset.range (k + 1), n.choose i := by
  classical
  calc
    (admissibleMissingSets n k).card ≤
        ∑ i ∈ Finset.range (k + 1),
          ((Finset.univ : Finset (Fin n)).powersetCard i).card := by
      exact Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (k + 1), n.choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]

def AdmissibleMissingSet (n k : Nat) :=
  ↥(admissibleMissingSets n k)

noncomputable instance admissibleMissingSetFintype (n k : Nat) :
    Fintype (AdmissibleMissingSet n k) := by
  dsimp [AdmissibleMissingSet]
  infer_instance

def canonicalCoveredSetFromMissing {n : Nat}
    (U : Finset (Fin n)) : Set (Fin n) :=
  {m | m ∉ U}

noncomputable def canonicalUncoveredMen {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter fun m ↦
    m ∉ canonicalRotationSupport P hstable
      (canonicalDeletionSourceFrontier D)

theorem canonicalRotationSupport_eq_coveredFromUncovered {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} (D : CanonicalDeletionFiber P hstable image) :
    canonicalRotationSupport P hstable
        (canonicalDeletionSourceFrontier D) =
      canonicalCoveredSetFromMissing (canonicalUncoveredMen D) := by
  classical
  ext m
  simp [canonicalCoveredSetFromMissing, canonicalUncoveredMen]

def CanonicalDeletionFiberWithUncoveredAtMost {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :=
  {D : CanonicalDeletionFiber P hstable image //
    (canonicalUncoveredMen D).card ≤ k}

def CanonicalDeletionFiberSupportCode {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :=
  Σ U : AdmissibleMissingSet n k,
    CanonicalDeletionFiberAtSupport P hstable image
      (canonicalCoveredSetFromMissing U.1)

noncomputable instance canonicalDeletionFiberSupportCodeFinite {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Finite (CanonicalDeletionFiberSupportCode P hstable image k) := by
  dsimp [CanonicalDeletionFiberSupportCode]
  infer_instance

noncomputable def canonicalDeletionFiberSupportEncode {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {k : Nat}
    (D : CanonicalDeletionFiberWithUncoveredAtMost P hstable image k) :
    CanonicalDeletionFiberSupportCode P hstable image k :=
  ⟨⟨canonicalUncoveredMen D.1,
      (mem_admissibleMissingSets_iff
        (n := n) (k := k) (canonicalUncoveredMen D.1)).2 D.2⟩,
    ⟨D.1, canonicalRotationSupport_eq_coveredFromUncovered D.1⟩⟩

theorem canonicalDeletionFiberSupportEncode_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {image : CodedStable P} {k : Nat} :
    Function.Injective
      (canonicalDeletionFiberSupportEncode
        (P := P) (hstable := hstable) (image := image) (k := k)) := by
  intro D E h
  have hval : D.1 = E.1 := by
    have := congrArg (fun z : CanonicalDeletionFiberSupportCode
      P hstable image k ↦ z.2.1) h
    exact this
  exact Subtype.ext hval

noncomputable instance canonicalDeletionFiberWithUncoveredAtMostFinite
    {n : Nat} (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Finite (CanonicalDeletionFiberWithUncoveredAtMost
      P hstable image k) :=
  Finite.of_injective
    (canonicalDeletionFiberSupportEncode
      (P := P) (hstable := hstable) (image := image) (k := k))
    (canonicalDeletionFiberSupportEncode_injective
      (P := P) (hstable := hstable) (image := image) (k := k))

theorem natCard_admissibleMissingSet_le_binomialPrefix (n k : Nat) :
    Nat.card (AdmissibleMissingSet n k) ≤
      ∑ i ∈ Finset.range (k + 1), n.choose i := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (AdmissibleMissingSet n k) =
        Fintype.card ↥(admissibleMissingSets n k) :=
      Fintype.card_congr (Equiv.refl _)
    _ = (admissibleMissingSets n k).card := Fintype.card_coe _
    _ ≤ ∑ i ∈ Finset.range (k + 1), n.choose i :=
      card_admissibleMissingSets_le_binomialPrefix n k

theorem natCard_canonicalDeletionFiberSupportCode_le {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Nat.card (CanonicalDeletionFiberSupportCode P hstable image k) ≤
      (∑ i ∈ Finset.range (k + 1), n.choose i) * 2 ^ (n / 4) := by
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
  change Nat.card (Σ U : AdmissibleMissingSet n k,
    CanonicalDeletionFiberAtSupport P hstable image
      (canonicalCoveredSetFromMissing U.1)) ≤ _
  rw [Nat.card_sigma]
  calc
    (∑ U : AdmissibleMissingSet n k,
        Nat.card (CanonicalDeletionFiberAtSupport P hstable image
          (canonicalCoveredSetFromMissing U.1))) ≤
        ∑ _U : AdmissibleMissingSet n k, 2 ^ (n / 4) := by
      exact Finset.sum_le_sum fun U _ ↦
        natCard_canonicalDeletionFiberAtSupport_le_two_pow_quarter
          P hstable image (canonicalCoveredSetFromMissing U.1)
    _ = Nat.card (AdmissibleMissingSet n k) * 2 ^ (n / 4) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (∑ i ∈ Finset.range (k + 1), n.choose i) * 2 ^ (n / 4) :=
      Nat.mul_le_mul_right _
        (natCard_admissibleMissingSet_le_binomialPrefix n k)

theorem natCard_canonicalDeletionFiberWithUncoveredAtMost_le {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (image : CodedStable P) (k : Nat) :
    Nat.card (CanonicalDeletionFiberWithUncoveredAtMost
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
  have hencode := Nat.card_le_card_of_injective
    (canonicalDeletionFiberSupportEncode
      (P := P) (hstable := hstable) (image := image) (k := k))
    (canonicalDeletionFiberSupportEncode_injective
      (P := P) (hstable := hstable) (image := image) (k := k))
  calc
    Nat.card (CanonicalDeletionFiberWithUncoveredAtMost
        P hstable image k) ≤
        Nat.card (CanonicalDeletionFiberSupportCode P hstable image k) :=
      hencode
    _ ≤ (∑ i ∈ Finset.range (k + 1), n.choose i) * 2 ^ (n / 4) :=
      natCard_canonicalDeletionFiberSupportCode_le P hstable image k
    _ = 2 ^ (n / 4) *
        (∑ i ∈ Finset.range (k + 1), n.choose i) := Nat.mul_comm _ _

end

end StableMatchingsJointCharging
