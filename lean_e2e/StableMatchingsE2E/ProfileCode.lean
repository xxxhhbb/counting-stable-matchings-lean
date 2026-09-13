import Mathlib
import StableMatchings355.Core

/-!
# Finite codes for stable-marriage profiles

This file gives proof-field-free finite codes for strict complete preference
profiles and perfect matchings on `Fin n`.  A preference permutation maps a
potential partner to their rank; smaller ranks are strictly preferred.
-/

namespace StableMatchingsE2E

/-- A proof-field-free code for an `n × n` strict complete preference profile.
Each permutation maps a possible partner to their rank (rank zero is best). -/
structure ProfileCode (n : Nat) where
  manRank : Fin n → Equiv.Perm (Fin n)
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving DecidableEq, Fintype

/-- A perfect matching is a permutation from men to women. -/
abbrev MatchingCode (n : Nat) := Equiv.Perm (Fin n)

/-- The canonical profile in which every agent ranks partners by their index. -/
def identityProfile (n : Nat) : ProfileCode n where
  manRank := fun _ => Equiv.refl _
  womanRank := fun _ => Equiv.refl _

instance profileCodeNonempty (n : Nat) : Nonempty (ProfileCode n) :=
  ⟨identityProfile n⟩

/-- Convert a finite profile code to the relation-based formal core. -/
def ProfileCode.toCore {n : Nat} (P : ProfileCode n) :
    StableMatchings355.Profile (Fin n) (Fin n) where
  manPref m a b := P.manRank m a < P.manRank m b
  womanPref w a b := P.womanRank w a < P.womanRank w b
  man_decidable := fun _ _ _ => inferInstance
  woman_decidable := fun _ _ _ => inferInstance
  man_asymm := fun _ _ _ hab hba => (LT.lt.asymm hab) hba
  woman_asymm := fun _ _ _ hab hba => (LT.lt.asymm hab) hba
  man_trans := fun _ _ _ _ hab hbc => LT.lt.trans hab hbc
  woman_trans := fun _ _ _ _ hab hbc => LT.lt.trans hab hbc
  man_total := by
    intro m a b hab
    have hrank : P.manRank m a ≠ P.manRank m b :=
      (P.manRank m).injective.ne hab
    exact lt_or_gt_of_ne hrank
  woman_total := by
    intro w a b hab
    have hrank : P.womanRank w a ≠ P.womanRank w b :=
      (P.womanRank w).injective.ne hab
    exact lt_or_gt_of_ne hrank

/-- Convert a matching permutation to the two-sided formal-core matching.
The woman's partner is necessarily `mu.symm w`. -/
def MatchingCode.toCore {n : Nat} (mu : MatchingCode n) :
    StableMatchings355.Matching (Fin n) (Fin n) where
  manPartner := mu
  womanPartner := mu.symm
  left_inv := mu.symm_apply_apply
  right_inv := mu.apply_symm_apply

/-- Recover a permutation code from any formal-core perfect matching. -/
def MatchingCode.ofCore {n : Nat}
    (mu : StableMatchings355.Matching (Fin n) (Fin n)) : MatchingCode n where
  toFun := mu.manPartner
  invFun := mu.womanPartner
  left_inv := mu.left_inv
  right_inv := mu.right_inv

@[simp] theorem MatchingCode.ofCore_apply {n : Nat}
    (mu : StableMatchings355.Matching (Fin n) (Fin n)) (m : Fin n) :
    MatchingCode.ofCore mu m = mu.manPartner m := rfl

@[simp] theorem MatchingCode.ofCore_symm_apply {n : Nat}
    (mu : StableMatchings355.Matching (Fin n) (Fin n)) (w : Fin n) :
    (MatchingCode.ofCore mu).symm w = mu.womanPartner w := rfl

/-- A pair blocks a coded matching when both endpoints strictly improve.
Smaller numerical rank means better, and the woman's incumbent is
`mu.symm w`. -/
def Blocks {n : Nat} (P : ProfileCode n) (mu : MatchingCode n)
    (m w : Fin n) : Prop :=
  P.manRank m w < P.manRank m (mu m) ∧
    P.womanRank w m < P.womanRank w (mu.symm w)

/-- A coded matching is stable when it has no blocking pair. -/
def Stable {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) : Prop :=
  ∀ m w, ¬ Blocks P mu m w

instance {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) (m w : Fin n) :
    Decidable (Blocks P mu m w) := by
  unfold Blocks
  infer_instance

instance {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) :
    Decidable (Stable P mu) := by
  unfold Stable
  infer_instance

/-- Explicitly named alias used at the code/core boundary. -/
abbrev StableCode {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) : Prop :=
  Stable P mu

theorem blocks_iff_core {n : Nat} (P : ProfileCode n) (mu : MatchingCode n)
    (m w : Fin n) :
    Blocks P mu m w ↔
      StableMatchings355.Blocks P.toCore mu.toCore m w := by
  rfl

theorem stableCode_iff_core {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) :
    StableCode P mu ↔ StableMatchings355.Stable P.toCore mu.toCore := by
  rfl

/-! ## Completeness of the permutation encoding

We use a wrapper type so that the preference-induced linear order and the
canonical order on `Fin n` remain distinct typeclass instances. -/

private structure RankedPartner (n : Nat) where
  val : Fin n
  deriving DecidableEq, Fintype

private def rankedPartnerEquiv (n : Nat) : Fin n ≃ RankedPartner n where
  toFun a := ⟨a⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl

private theorem strictTotalOrderOfCore {n : Nat} (r : Fin n → Fin n → Prop)
    (hasymm : ∀ a b, r a b → ¬ r b a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a) :
    IsStrictTotalOrder (Fin n) r where
  irrefl a haa := hasymm a a haa haa
  trans := htrans
  trichotomous a b hnab hnba := by
    by_contra hab
    rcases htotal a b hab with hab' | hba'
    · exact hnab hab'
    · exact hnba hba'

private noncomputable def rankPermutation {n : Nat} (r : Fin n → Fin n → Prop)
    (hdec : DecidableRel r) (hsto : IsStrictTotalOrder (Fin n) r) :
    Equiv.Perm (Fin n) := by
  let rr : RankedPartner n → RankedPartner n → Prop := fun a b => r a.val b.val
  letI : DecidableRel rr := fun a b => hdec a.val b.val
  letI : IsStrictTotalOrder (RankedPartner n) rr := {
    irrefl a := hsto.irrefl a.val
    trans a b c := hsto.trans a.val b.val c.val
    trichotomous a b hnab hnba := by
      cases a with
      | mk av =>
        cases b with
        | mk bv =>
          congr 1
          exact hsto.trichotomous av bv hnab hnba
  }
  letI : LinearOrder (RankedPartner n) := linearOrderOfSTO rr
  let sorted : Fin n ≃o RankedPartner n :=
    Fintype.orderIsoFinOfCardEq (RankedPartner n)
      ((Fintype.card_congr (rankedPartnerEquiv n).symm).trans (Fintype.card_fin n))
  exact (rankedPartnerEquiv n).trans sorted.symm.toEquiv

private theorem rankPermutation_lt_iff {n : Nat} (r : Fin n → Fin n → Prop)
    (hdec : DecidableRel r) (hsto : IsStrictTotalOrder (Fin n) r)
    (a b : Fin n) :
    rankPermutation r hdec hsto a < rankPermutation r hdec hsto b ↔ r a b := by
  let rr : RankedPartner n → RankedPartner n → Prop := fun a b => r a.val b.val
  letI : DecidableRel rr := fun a b => hdec a.val b.val
  letI : IsStrictTotalOrder (RankedPartner n) rr := {
    irrefl a := hsto.irrefl a.val
    trans a b c := hsto.trans a.val b.val c.val
    trichotomous a b hnab hnba := by
      cases a with
      | mk av =>
        cases b with
        | mk bv =>
          congr 1
          exact hsto.trichotomous av bv hnab hnba
  }
  letI : LinearOrder (RankedPartner n) := linearOrderOfSTO rr
  let sorted : Fin n ≃o RankedPartner n :=
    Fintype.orderIsoFinOfCardEq (RankedPartner n)
      ((Fintype.card_congr (rankedPartnerEquiv n).symm).trans (Fintype.card_fin n))
  change sorted.symm (rankedPartnerEquiv n a) <
      sorted.symm (rankedPartnerEquiv n b) ↔ r a b
  rw [sorted.symm.lt_iff_lt]
  rfl

/-- Rank every strict total preference relation in a formal-core profile.
This proves that `ProfileCode` loses no relation-based strict complete profile. -/
noncomputable def ProfileCode.ofCore {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n)) : ProfileCode n where
  manRank m := rankPermutation (P.manPref m) (P.man_decidable m)
    (strictTotalOrderOfCore (P.manPref m) (P.man_asymm m)
      (P.man_trans m) (P.man_total m))
  womanRank w := rankPermutation (P.womanPref w) (P.woman_decidable w)
    (strictTotalOrderOfCore (P.womanPref w) (P.woman_asymm w)
      (P.woman_trans w) (P.woman_total w))

theorem ProfileCode.ofCore_manPref_iff {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n)) (m a b : Fin n) :
    ((ProfileCode.ofCore P).manRank m a < (ProfileCode.ofCore P).manRank m b) ↔
      P.manPref m a b := by
  exact rankPermutation_lt_iff (P.manPref m) (P.man_decidable m)
    (strictTotalOrderOfCore (P.manPref m) (P.man_asymm m)
      (P.man_trans m) (P.man_total m)) a b

theorem ProfileCode.ofCore_womanPref_iff {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n)) (w a b : Fin n) :
    ((ProfileCode.ofCore P).womanRank w a < (ProfileCode.ofCore P).womanRank w b) ↔
      P.womanPref w a b := by
  exact rankPermutation_lt_iff (P.womanPref w) (P.woman_decidable w)
    (strictTotalOrderOfCore (P.womanPref w) (P.woman_asymm w)
      (P.woman_trans w) (P.woman_total w)) a b

theorem stable_ofCore_iff {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n)) (mu : MatchingCode n) :
    Stable (ProfileCode.ofCore P) mu ↔ StableMatchings355.Stable P mu.toCore := by
  constructor
  · intro h m w hblocks
    apply h m w
    exact ⟨(ProfileCode.ofCore_manPref_iff P m w (mu m)).2 hblocks.1,
      (ProfileCode.ofCore_womanPref_iff P w m (mu.symm w)).2 hblocks.2⟩
  · intro h m w hblocks
    apply h m w
    exact ⟨(ProfileCode.ofCore_manPref_iff P m w (mu m)).1 hblocks.1,
      (ProfileCode.ofCore_womanPref_iff P w m (mu.symm w)).1 hblocks.2⟩

/-- Simultaneously encoding a relation profile and a formal-core matching
preserves stability.  Thus both finite universes are complete. -/
theorem stable_full_ofCore_iff {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n))
    (mu : StableMatchings355.Matching (Fin n) (Fin n)) :
    Stable (ProfileCode.ofCore P) (MatchingCode.ofCore mu) ↔
      StableMatchings355.Stable P mu := by
  constructor
  · intro h m w hblocks
    apply h m w
    exact ⟨(ProfileCode.ofCore_manPref_iff P m w (mu.manPartner m)).2 hblocks.1,
      (ProfileCode.ofCore_womanPref_iff P w m (mu.womanPartner w)).2 hblocks.2⟩
  · intro h m w hblocks
    apply h m w
    exact ⟨(ProfileCode.ofCore_manPref_iff P m w (mu.manPartner m)).1 hblocks.1,
      (ProfileCode.ofCore_womanPref_iff P w m (mu.womanPartner w)).1 hblocks.2⟩

theorem every_core_profile_has_complete_code {n : Nat}
    (P : StableMatchings355.Profile (Fin n) (Fin n)) :
    ∃ Q : ProfileCode n,
      (∀ m a b, Q.manRank m a < Q.manRank m b ↔ P.manPref m a b) ∧
      (∀ w a b, Q.womanRank w a < Q.womanRank w b ↔ P.womanPref w a b) := by
  exact ⟨ProfileCode.ofCore P, ProfileCode.ofCore_manPref_iff P,
    ProfileCode.ofCore_womanPref_iff P⟩

/-- The finite set of all stable matching codes for `P`. -/
def stableSet {n : Nat} (P : ProfileCode n) : Finset (MatchingCode n) :=
  Finset.univ.filter (Stable P)

theorem mem_stableSet_iff {n : Nat} (P : ProfileCode n) (mu : MatchingCode n) :
    mu ∈ stableSet P ↔ Stable P mu := by
  simp [stableSet]

/-- Number of stable matchings of a coded profile. -/
def stableCount {n : Nat} (P : ProfileCode n) : Nat :=
  (stableSet P).card

/-- Maximum number of stable matchings among all coded `n × n` profiles. -/
def SM (n : Nat) : Nat :=
  Finset.univ.sup (stableCount : ProfileCode n → Nat)

theorem profile_universe_nonempty (n : Nat) :
    (Finset.univ : Finset (ProfileCode n)).Nonempty := by
  exact ⟨identityProfile n, Finset.mem_univ _⟩

/-- Every profile's stable count is bounded by the finite maximum. -/
theorem SM_spec {n : Nat} (P : ProfileCode n) : stableCount P ≤ SM n := by
  exact Finset.le_sup (s := (Finset.univ : Finset (ProfileCode n)))
    (f := stableCount) (Finset.mem_univ P)

/-- The finite maximum is attained by an actual coded profile. -/
theorem exists_profile_attaining_SM (n : Nat) :
    ∃ P : ProfileCode n, stableCount P = SM n := by
  classical
  obtain ⟨P, -, hP⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (ProfileCode n)) (profile_universe_nonempty n) stableCount
  exact ⟨P, hP.symm⟩

private theorem subsingleton_matchingCode_zero :
    Subsingleton (MatchingCode 0) := by infer_instance

private theorem stable_zero (mu : MatchingCode 0) :
    Stable (identityProfile 0) mu := by
  intro m
  exact Fin.elim0 m

theorem stableSet_zero (P : ProfileCode 0) : stableSet P = Finset.univ := by
  ext mu
  simp only [mem_stableSet_iff, Finset.mem_univ, iff_true]
  intro m
  exact Fin.elim0 m

theorem stableCount_zero (P : ProfileCode 0) : stableCount P = 1 := by
  rw [stableCount, stableSet_zero]
  exact Fintype.card_unique

/-- At size zero there is one empty profile and one empty stable matching. -/
theorem SM_zero : SM 0 = 1 := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM 0
  rw [← hP, stableCount_zero]

end StableMatchingsE2E
