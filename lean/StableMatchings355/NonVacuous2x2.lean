import StableMatchings355.Interval

namespace StableMatchings355

def boolProfile : Profile Bool Bool where
  manPref := fun m a b => a = m /\ b ≠ m
  womanPref := fun w a b => a ≠ w /\ b = w
  man_decidable := fun _ _ _ => inferInstance
  woman_decidable := fun _ _ _ => inferInstance
  man_asymm := by decide
  woman_asymm := by decide
  man_trans := by decide
  woman_trans := by decide
  man_total := by decide
  woman_total := by decide

def boolIdentity : Matching Bool Bool where
  manPartner := fun m => m
  womanPartner := fun w => w
  left_inv := by simp
  right_inv := by simp

def boolSwap : Matching Bool Bool where
  manPartner := Bool.not
  womanPartner := Bool.not
  left_inv := by intro m; cases m <;> rfl
  right_inv := by intro w; cases w <;> rfl

theorem boolIdentity_stable : Stable boolProfile boolIdentity := by
  intro m w h
  cases m <;> cases w <;> simp [Blocks, boolProfile, boolIdentity] at h

theorem boolSwap_stable : Stable boolProfile boolSwap := by
  intro m w h
  cases m <;> cases w <;> simp [Blocks, boolProfile, boolSwap] at h

theorem bool_matching_cases (mu : Matching Bool Bool) :
    ((mu.manPartner false = false /\ mu.manPartner true = true) /\
      (mu.womanPartner false = false /\ mu.womanPartner true = true)) \/
    ((mu.manPartner false = true /\ mu.manPartner true = false) /\
      (mu.womanPartner false = true /\ mu.womanPartner true = false)) := by
  cases h0 : mu.manPartner false <;> cases h1 : mu.manPartner true
  · have heq : false = true := mu.manPartner_injective (h0.trans h1.symm)
    contradiction
  · left
    have hw0 := matched_woman_partner mu h0
    have hw1 := matched_woman_partner mu h1
    simp_all
  · right
    have hw0 := matched_woman_partner mu h1
    have hw1 := matched_woman_partner mu h0
    simp_all
  · have heq : false = true := mu.manPartner_injective (h0.trans h1.symm)
    contradiction

theorem boolProfile_hasMenJoin : HasMenJoin boolProfile := by
  intro mu sigma _ _
  rcases bool_matching_cases mu with hmu | hmu <;>
    rcases bool_matching_cases sigma with hsigma | hsigma
  · refine ⟨mu, ?_, ?_⟩
    · intro m; cases m <;> simp_all [boolProfile]
    · intro w; cases w <;> simp_all [boolProfile]
  · refine ⟨mu, ?_, ?_⟩
    · intro m; cases m <;> simp_all [boolProfile]
    · intro w; cases w <;> simp_all [boolProfile]
  · refine ⟨sigma, ?_, ?_⟩
    · intro m; cases m <;> simp_all [boolProfile]
    · intro w; cases w <;> simp_all [boolProfile]
  · refine ⟨mu, ?_, ?_⟩
    · intro m; cases m <;> simp_all [boolProfile]
    · intro w; cases w <;> simp_all [boolProfile]

def boolTargetPartners : RankedPartners boolProfile false 2 where
  partner := fun i => if i.val = 0 then false else true
  injective := by
    intro i j h
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · simp [hi, hj] at h
    · simp [hi, hj] at h
    · omega
  rank_spec := by
    intro i j
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
      simp [boolProfile, hi, hj] <;> omega

/- All premises of the lower-barrier theorem are instantiated, including the
   strict step 0 < 1.  Here sigma is the identity stable matching; mu=nu is
   the swapped stable matching, and the revealed man `true` keeps woman
   `false`, the target man's better stable partner. -/
theorem lower_barrier_nonvacuous_2x2 :
    (0 : Fin 2).val < (1 : Fin 2).val := by
  exact revealed_lower_barrier boolProfile boolProfile_hasMenJoin
    (m := false) (p := true) boolTargetPartners
    boolIdentity boolSwap boolSwap
    boolIdentity_stable boolSwap_stable boolSwap_stable
    (h := 0) (j := 1) (t := 1)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by decide)

end StableMatchings355
