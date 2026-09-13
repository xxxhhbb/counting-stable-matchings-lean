import StableMatchingsE2E.StablePairApplication
import StableMatchingsE2E.StablePairEqualityStructure

namespace StableMatchingsE2E
open scoped Classical

def StablePairEquality {n : Nat} (P : ProfileCode n) : Prop :=
  (stableCount P)^4 = 2^(stablePairSet P).card

theorem nonempty_stableState_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : Nonempty (StableState P) := by
  by_contra hn
  haveI : IsEmpty (StableState P) := not_nonempty_iff.mp hn
  have hz : stableCount P = 0 := by rw [← card_stableState]; exact Fintype.card_eq_zero
  have hpos : 0 < 2^(stablePairSet P).card := by positivity
  unfold StablePairEquality at heq
  rw [hz] at heq
  norm_num at heq
  omega

theorem supportExcess_eq_zero_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : supportExcess P = 0 := by
  have hb := stableCount_fourth_penalized_stablePairs P
  rw [heq] at hb
  have hbase : 0 < 2^(stablePairSet P).card := by positivity
  have hp := Nat.le_of_mul_le_mul_left hb hbase
  by_contra hn
  have hs : 6561^(supportExcess P) < 8192^(supportExcess P) := Nat.pow_lt_pow_left (by decide) hn
  omega

theorem all_supports_binary_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : ∀ r : IrreducibleState P, r.support.card = 2 := by
  have hz := supportExcess_eq_zero_of_stablePairEquality P heq
  intro r
  have hzero : r.support.card-2 = 0 := (Finset.sum_eq_zero_iff.mp hz) r (Finset.mem_univ _)
  have hge := r.support_card_ge_two
  omega

noncomputable def binarySupportGraph {n : Nat} (P : ProfileCode n)
    (hb : ∀ r : IrreducibleState P, r.support.card = 2) :
    LabeledMultigraph (Fin n) (IrreducibleState P) where
  vertices := Finset.univ
  edges := Finset.univ
  ends := IrreducibleState.support
  ends_card := fun r _ ↦ hb r
  ends_subset := fun r _ ↦ Finset.subset_univ _

theorem binarySupportGraph_matchingCount {n : Nat} (P : ProfileCode n)
    (hb : ∀ r : IrreducibleState P, r.support.card = 2) :
    (binarySupportGraph P hb).matchingCount = (irreducibleSupportHypergraph P).matchingCount := by
  have hf : (binarySupportGraph P hb).matchingFamily = (irreducibleSupportHypergraph P).matchingFamily := by
    ext S
    simp [LabeledMultigraph.mem_matchingFamily_iff,LabeledHypergraph.mem_matchingFamily_iff,
      LabeledMultigraph.IsMatching,binarySupportGraph,LabeledMultigraph.toHypergraph,irreducibleSupportHypergraph]
  exact congrArg Finset.card hf

theorem supportMatchingCount_eq_stableCount_of_equality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : (irreducibleSupportHypergraph P).matchingCount = stableCount P := by
  letI := nonempty_stableState_of_stablePairEquality P heq
  have hlo := stableCount_le_supportMatchingCount P
  have hhi := LabeledHypergraph.matchingCount_fourth_le_two_pow (irreducibleSupportHypergraph P)
    Finset.univ (fun r ↦ Finset.subset_univ _) (fun r ↦ r.support_card_ge_two)
    (irreducibleSupport_no_isolated_double P)
  have hinc := stablePairSet_card_eq_vertices_add_supports P
  have hhi' : (irreducibleSupportHypergraph P).matchingCount^4 ≤ 2^(stablePairSet P).card := by
    simpa [irreducibleSupportHypergraph,← hinc] using hhi
  apply le_antisymm ?_ hlo
  by_contra hn
  have hs := Nat.pow_lt_pow_left (lt_of_not_ge hn) (by decide : 4 ≠ 0)
  rw [heq] at hs
  omega

theorem binarySupportGraph_sharpEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) :
    (binarySupportGraph P (all_supports_binary_of_stablePairEquality P heq)).SharpEquality := by
  letI := nonempty_stableState_of_stablePairEquality P heq
  let hb := all_supports_binary_of_stablePairEquality P heq
  let G := binarySupportGraph P hb
  have hq : G.doubleComponentCount = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hs := (LabeledMultigraph.mem_doubleComponents_iff G S).mp hS
    apply irreducibleSupport_no_isolated_double P S
    exact ⟨hs.2.1,fun r hm ↦ hs.2.2.1.2 r (Finset.mem_univ _) hm,hs.2.2.2⟩
  have hc : G.vertexCount+2*G.edgeCount = (stablePairSet P).card := by
    rw [stablePairSet_card_eq_vertices_add_supports P]
    simp [G,binarySupportGraph,LabeledMultigraph.vertexCount,LabeledMultigraph.edgeCount,hb,Nat.mul_comm]
  have hz : G.matchingCount = stableCount P := (binarySupportGraph_matchingCount P hb).trans
    (supportMatchingCount_eq_stableCount_of_equality P heq)
  change G.SharpEquality
  unfold LabeledMultigraph.SharpEquality
  rw [hq,hc,hz]
  simpa [StablePairEquality] using heq

theorem unique_support_label_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) (m : Fin n) :
    ∃ r : IrreducibleState P, m ∈ r.support ∧ ∀ s : IrreducibleState P, m ∈ s.support → s=r := by
  let hb := all_supports_binary_of_stablePairEquality P heq
  let G := binarySupportGraph P hb
  have hno : ∀ S : Finset (Fin n), S.card=2 → G.IsIsolatedSupport S → (G.edgesOn S).card ≤ 1 := by
    intro S hS hiso
    exact isolated_binary_support_card_le_one P S hS (fun t ht ↦ hiso.2 t (Finset.mem_univ _) ht)
  obtain ⟨r,hr,hm,hu⟩ := LabeledMultigraph.unique_incident_edge_of_sharpEquality G
    (binarySupportGraph_sharpEquality P heq) hno m (Finset.mem_univ _)
  exact ⟨r,hm,fun s hs ↦ hu s (Finset.mem_univ _) hs⟩

theorem irreducible_order_trivial_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : ∀ r s : IrreducibleState P, r ≤ s → r=s := by
  letI := nonempty_stableState_of_stablePairEquality P heq
  let H := irreducibleSupportHypergraph P
  have hcomp : H.OverlapComparable (· ≤ ·) := fun r s _ hm ↦ irreducibleSupport_overlap_comparable P r s hm
  have hsub := LabeledHypergraph.antichainFamily_subset_matchingFamily (· ≤ ·) H hcomp
  have hcard : H.matchingFamily.card ≤ (LabeledHypergraph.antichainFamily
      ((· ≤ ·) : IrreducibleState P → _ → Prop)).card := by
    change H.matchingCount ≤ LabeledHypergraph.antichainCount _
    rw [← stableCount_eq_antichainCount]
    exact (supportMatchingCount_eq_stableCount_of_equality P heq).le
  have hf := Finset.eq_of_subset_of_card_le hsub hcard
  intro r s hrs
  by_contra hne
  have hm : H.IsMatching {r,s} := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro m hma hmb
    obtain ⟨t,ht,hu⟩ := unique_support_label_of_stablePairEquality P heq m
    exact hab ((hu a hma).trans (hu b hmb).symm)
  have hmem : {r,s} ∈ LabeledHypergraph.antichainFamily ((· ≤ ·) : IrreducibleState P → _ → Prop) := by
    rw [hf]
    exact (LabeledHypergraph.mem_matchingFamily_iff H _).mpr hm
  have ha := (LabeledHypergraph.mem_antichainFamily_iff _ _).mp hmem
  exact (ha r (by simp) s (by simp) hne).1 hrs

/-- Structural equality condition phrased entirely in the actual stable-state
model: binary supports partition the men and their label order is an antichain. -/
def IndependentBinaryCover {n : Nat} (P : ProfileCode n) : Prop :=
  Nonempty (StableState P) ∧ (∀ r : IrreducibleState P, r.support.card = 2) ∧
    (∀ m : Fin n, ∃ r : IrreducibleState P, m ∈ r.support ∧
      ∀ s : IrreducibleState P, m ∈ s.support → s=r) ∧
    (∀ r s : IrreducibleState P, r ≤ s → r=s)

theorem independentBinaryCover_of_stablePairEquality {n : Nat} (P : ProfileCode n)
    (heq : StablePairEquality P) : IndependentBinaryCover P :=
  ⟨nonempty_stableState_of_stablePairEquality P heq,
    all_supports_binary_of_stablePairEquality P heq,
    unique_support_label_of_stablePairEquality P heq,
    irreducible_order_trivial_of_stablePairEquality P heq⟩

theorem stablePairEquality_of_independentBinaryCover {n : Nat} (P : ProfileCode n)
    (h : IndependentBinaryCover P) : StablePairEquality P := by
  letI := h.1
  have hlabels : ∀ m : Fin n, (participantLabels P m).card=1 := by
    intro m
    obtain ⟨r,hr,hu⟩ := h.2.2.1 m
    have hf : participantLabels P m = {r} := by
      ext s
      simp only [participantLabels,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      exact ⟨hu s,fun he ↦ he.symm ▸ hr⟩
    rw [hf]; simp
  have hdouble := support_incidence_double_count P
  simp only [hlabels,h.2.1,Finset.sum_const] at hdouble
  have hn : n = 2*Fintype.card (IrreducibleState P) := by simpa [Nat.mul_comm] using hdouble
  have hm : (stablePairSet P).card = 4*Fintype.card (IrreducibleState P) := by
    rw [stablePairSet_card_eq_vertices_add_supports]
    simp only [h.2.1,Finset.sum_const]
    simp only [Finset.card_univ,smul_eq_mul,Nat.cast_id]
    omega
  have hf : LabeledHypergraph.antichainFamily ((· ≤ ·) : IrreducibleState P → _ → Prop) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro S
    apply (LabeledHypergraph.mem_antichainFamily_iff _ _).mpr
    intro r hr s hs hne
    exact ⟨fun hrs ↦ hne (h.2.2.2 r s hrs),fun hsr ↦ hne (h.2.2.2 s r hsr).symm⟩
  have hcount : stableCount P = 2^Fintype.card (IrreducibleState P) := by
    rw [stableCount_eq_antichainCount]
    unfold LabeledHypergraph.antichainCount
    rw [hf]
    simp
  unfold StablePairEquality
  rw [hcount,hm,← pow_mul,Nat.mul_comm]

theorem stablePairEquality_iff_independentBinaryCover {n : Nat} (P : ProfileCode n) :
    StablePairEquality P ↔ IndependentBinaryCover P :=
  ⟨independentBinaryCover_of_stablePairEquality P,stablePairEquality_of_independentBinaryCover P⟩

end StableMatchingsE2E
