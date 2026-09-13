import StableMatchingsE2E.ProfileCode

/-! Formal interfaces only. No external algorithm is declared as an axiom.
The incomplete-list interface below is on the fixed, balanced matched vertex
sets; the common-matched-set theorem for partial matchings is still separate.
-/
namespace StableMatchingsE2E
open scoped BigOperators Classical

structure AcceptableCompletion {n : Nat} (P : ProfileCode n) where
  acceptable : Fin n → Fin n → Prop
  men_before : ∀ m w v, acceptable m w → ¬ acceptable m v →
    P.manRank m w < P.manRank m v
  women_before : ∀ w m u, acceptable m w → ¬ acceptable u w →
    P.womanRank w m < P.womanRank w u

def AcceptableCompletion.StablePerfect {n : Nat} {P : ProfileCode n}
    (C : AcceptableCompletion P) (mu : MatchingCode n) : Prop :=
  (∀ m, C.acceptable m (mu m)) ∧
    ∀ m w, C.acceptable m w → ¬ Blocks P mu m w

theorem AcceptableCompletion.stable_of_stablePerfect {n : Nat} {P : ProfileCode n}
    (C : AcceptableCompletion P) {mu : MatchingCode n} (h : C.StablePerfect mu) :
    Stable P mu := by
  intro m w hb
  by_cases ha : C.acceptable m w
  · exact h.2 m w ha hb
  · exact (not_lt_of_gt (C.men_before m (mu m) w (h.1 m) ha)) hb.1

theorem AcceptableCompletion.stablePerfect_iff {n : Nat} {P : ProfileCode n}
    (C : AcceptableCompletion P) (mu : MatchingCode n) :
    C.StablePerfect mu ↔ (∀ m, C.acceptable m (mu m)) ∧ Stable P mu := by
  constructor
  · intro h
    exact ⟨h.1, C.stable_of_stablePerfect h⟩
  · intro h
    exact ⟨h.1, fun m w _ ↦ h.2 m w⟩

noncomputable def AcceptableCompletion.stableEmbedding {n : Nat} {P : ProfileCode n}
    (C : AcceptableCompletion P) :
    {mu : MatchingCode n // C.StablePerfect mu} ↪ {mu : MatchingCode n // Stable P mu} where
  toFun mu := ⟨mu.val, C.stable_of_stablePerfect mu.property⟩
  inj' := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : {mu : MatchingCode n // Stable P mu} ↦ z.val) h)

theorem AcceptableCompletion.count_le {n : Nat} {P : ProfileCode n}
    (C : AcceptableCompletion P) :
    Nat.card {mu : MatchingCode n // C.StablePerfect mu} ≤ stableCount P := by
  have h := Nat.card_le_card_of_injective _ C.stableEmbedding.injective
  convert h using 1
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype (stableSet P) (fun mu ↦ mem_stableSet_iff P mu)).symm

theorem popular_candidate_binomial (c : ℝ) (N : Nat) :
    ∑ i ∈ Finset.range (N+1), c^i * (2 * Real.sqrt c)^(N-i) * (N.choose i : ℝ) =
      (c + 2 * Real.sqrt c)^N := by
  exact (add_pow c (2 * Real.sqrt c) N).symm

theorem popular_base_certificate :
    (2078/625 : ℝ) + 2 * Real.sqrt (2078/625) < 69717/10000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2078/625)
  have hp := Real.sqrt_nonneg (2078/625 : ℝ)
  nlinarith

end StableMatchingsE2E
