import StableMatchings355.Interval

namespace StableMatchings355

/- A concrete finite inhabitant showing that RankedPartners is not vacuous.
   One participant on each side has the unique complete strict preference. -/
def unitProfile : Profile Unit Unit where
  manPref := fun _ _ _ => False
  womanPref := fun _ _ _ => False
  man_decidable := fun _ _ _ => inferInstance
  woman_decidable := fun _ _ _ => inferInstance
  man_asymm := by simp
  woman_asymm := by simp
  man_trans := by simp
  woman_trans := by simp
  man_total := by
    intro _ a b hne
    exact False.elim (hne (Subsingleton.elim a b))
  woman_total := by
    intro _ a b hne
    exact False.elim (hne (Subsingleton.elim a b))

def unitMatching : Matching Unit Unit where
  manPartner := fun _ => ()
  womanPartner := fun _ => ()
  left_inv := by simp
  right_inv := by simp

theorem unitMatching_stable : Stable unitProfile unitMatching := by
  intro m w h
  exact h.1

def unitRankedPartners : RankedPartners unitProfile () 1 where
  partner := fun _ => ()
  injective := by
    intro a b _
    exact Subsingleton.elim a b
  rank_spec := by
    intro i j
    constructor
    · intro h
      exact False.elim h
    · intro h
      have hij : i = j := Subsingleton.elim i j
      exact False.elim ((Nat.lt_irrefl j.val) (by simpa [hij] using h))

/- A nontrivial two-entry ranked table.  This profile is used only to witness
   that the finite rank interface permits genuine strict index inequalities;
   its two sides intentionally have different cardinalities, so no matching
   is asserted here. -/
def twoRankProfile : Profile Unit (Fin 2) where
  manPref := fun _ a b => a.val < b.val
  womanPref := fun _ _ _ => False
  man_decidable := fun _ _ _ => inferInstance
  woman_decidable := fun _ _ _ => inferInstance
  man_asymm := by
    intro _ a b hab hba
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hab)) hba
  woman_asymm := by simp
  man_trans := by
    intro _ a b c hab hbc
    exact Nat.lt_trans hab hbc
  woman_trans := by simp
  man_total := by
    intro _ a b hne
    have hvne : a.val ≠ b.val := by
      intro h
      exact hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hvne with h | h
    · exact Or.inl h
    · exact Or.inr h
  woman_total := by
    intro _ a b hne
    exact False.elim (hne (Subsingleton.elim a b))

def twoRankedPartners : RankedPartners twoRankProfile () 2 where
  partner := fun i => i
  injective := fun _ _ h => h
  rank_spec := by simp [twoRankProfile]

theorem twoRankedPartners_has_strict_step :
    (twoRankedPartners.partner ⟨0, by decide⟩).val <
      (twoRankedPartners.partner ⟨1, by decide⟩).val := by decide

end StableMatchings355
