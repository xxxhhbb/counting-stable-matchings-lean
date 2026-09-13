import StableMatchingsE2E.StableRotationNoReturn
import StableMatchingsE2E.FiniteIdealAntichain

namespace StableMatchingsE2E
open scoped Classical

theorem card_stableState {n : Nat} (P : ProfileCode n) :
    Fintype.card (StableState P) = stableCount P :=
  Fintype.card_of_subtype (stableSet P) (mem_stableSet_iff P)

noncomputable def stableStateAntichainEquiv {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] : StableState P ≃
      {S : Finset (IrreducibleState P) // LabeledHypergraph.IsAntichain (· ≤ ·) S} :=
  (stableStateIdealEquiv P).toEquiv.trans FiniteIdealAntichain.equiv

theorem stableCount_eq_antichainCount {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] :
    stableCount P = LabeledHypergraph.antichainCount ((· ≤ ·) : IrreducibleState P → _ → Prop) := by
  classical
  have hc := Fintype.card_congr (stableStateAntichainEquiv P)
  rw [card_stableState] at hc
  have ha := Fintype.card_of_subtype
    (LabeledHypergraph.antichainFamily ((· ≤ ·) : IrreducibleState P → _ → Prop))
    (LabeledHypergraph.mem_antichainFamily_iff _)
  exact hc.trans ha

theorem stableCount_le_supportMatchingCount {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] :
    stableCount P ≤ (irreducibleSupportHypergraph P).matchingCount := by
  classical
  rw [stableCount_eq_antichainCount]
  apply LabeledHypergraph.antichainCount_le_matchingCount
  intro r s hne hmeet
  exact irreducibleSupport_overlap_comparable P r s hmeet

noncomputable def supportExcess {n : Nat} (P : ProfileCode n) : Nat :=
  ∑ r : IrreducibleState P, (r.support.card-2)

/-- End-to-end stable-pair bound on actual profile codes, with the exact
penalty for nonbinary canonical irreducible supports. -/
theorem stableCount_fourth_penalized_stablePairs {n : Nat} (P : ProfileCode n) :
    (stableCount P)^4 * 8192^(supportExcess P) ≤
      2^(stablePairSet P).card * 6561^(supportExcess P) := by
  classical
  by_cases hn : Nonempty (StableState P)
  · letI := hn
    have hb := LabeledHypergraph.matchingCount_fourth_bound (irreducibleSupportHypergraph P)
      Finset.univ (fun r ↦ Finset.subset_univ _) (fun r ↦ r.support_card_ge_two)
      (irreducibleSupport_no_isolated_double P)
    have hinc := stablePairSet_card_eq_vertices_add_supports P
    have hp := Nat.mul_le_mul_right (8192^(supportExcess P))
      (Nat.pow_le_pow_left (stableCount_le_supportMatchingCount P) 4)
    apply hp.trans
    simpa [supportExcess,irreducibleSupportHypergraph,← hinc] using hb
  · haveI : IsEmpty (StableState P) := not_nonempty_iff.mp hn
    have hz : stableCount P = 0 := by rw [← card_stableState]; exact Fintype.card_eq_zero
    simp [hz]

/-- The sharp stable-pair upper bound, for every actual strict complete
profile, with no rotation-system hypothesis. Fourth powers avoid roots. -/
theorem stableCount_fourth_le_two_pow_stablePairs {n : Nat} (P : ProfileCode n) :
    (stableCount P)^4 ≤ 2^(stablePairSet P).card := by
  have hb := stableCount_fourth_penalized_stablePairs P
  have hp : 6561^(supportExcess P) ≤ 8192^(supportExcess P) := Nat.pow_le_pow_left (by decide) _
  have hh := hb.trans (Nat.mul_le_mul_left _ hp)
  exact Nat.le_of_mul_le_mul_right hh (by positivity)

end StableMatchingsE2E
