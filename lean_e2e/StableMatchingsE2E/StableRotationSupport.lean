import StableMatchingsE2E.StableMatchingLattice
import StableMatchingsE2E.StablePairHypergraph

namespace StableMatchingsE2E

noncomputable instance irreducibleStateFintype {n : Nat} (P : ProfileCode n) :
    Fintype (IrreducibleState P) := by
  classical
  infer_instance

namespace IrreducibleState
variable {n : Nat} {P : ProfileCode n}

/-- Finite irreducibility gives a greatest strict predecessor, constructed in
the lattice of actual stable matchings. -/
theorem exists_predecessor (r : IrreducibleState P) :
    ∃ p : StableState P, p < r.val ∧ ∀ a : StableState P, a < r.val → a ≤ p := by
  classical
  letI : Nonempty (StableState P) := ⟨r.val⟩
  letI : OrderBot (StableState P) := Fintype.toOrderBot (StableState P)
  let S : Finset (StableState P) := Finset.univ.filter (fun a ↦ a < r.val)
  have hle : S.sup id ≤ r.val := by
    apply Finset.sup_le
    intro a ha
    exact (Finset.mem_filter.mp ha).2.le
  have hne : S.sup id ≠ r.val := by
    intro he
    obtain ⟨a,ha,heq⟩ := r.property.finset_sup_eq he
    have hlt := (Finset.mem_filter.mp ha).2
    exact hlt.ne heq
  refine ⟨S.sup id,lt_of_le_of_ne hle hne,?_⟩
  intro a ha
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ a,ha⟩)

noncomputable def predecessor (r : IrreducibleState P) : StableState P :=
  Classical.choose (exists_predecessor r)

theorem predecessor_lt (r : IrreducibleState P) : r.predecessor < r.val :=
  (Classical.choose_spec (exists_predecessor r)).1

theorem le_predecessor {r : IrreducibleState P} {a : StableState P}
    (ha : a < r.val) : a ≤ r.predecessor :=
  (Classical.choose_spec (exists_predecessor r)).2 a ha

theorem predecessor_unique (r : IrreducibleState P) {p : StableState P}
    (hp : p < r.val) (hmax : ∀ a : StableState P, a < r.val → a ≤ p) :
    p = r.predecessor := le_antisymm (le_predecessor hp) (hmax _ r.predecessor_lt)

noncomputable def support (r : IrreducibleState P) : Finset (Fin n) :=
  StableState.changedMen r.predecessor r.val

theorem support_card_ge_two (r : IrreducibleState P) : 2 ≤ r.support.card :=
  StableState.changedMen_card_ge_two r.predecessor_lt.ne

theorem rank_predecessor_lt {r : IrreducibleState P} {m : Fin n} (hm : m ∈ r.support) :
    r.predecessor.rank m < r.val.rank m :=
  StableState.rank_strict_of_le_of_changed r.predecessor_lt.le hm

/-- Any changed coordinate detects precisely the ideal event r <= a. -/
theorem le_iff_rank_le {r : IrreducibleState P} {m : Fin n}
    (hm : m ∈ r.support) (a : StableState P) :
    r.val ≤ a ↔ r.val.rank m ≤ a.rank m := by
  constructor
  · intro h; exact h m
  · intro hrank
    by_contra hnot
    have hlt : r.val ⊓ a < r.val := by
      apply lt_of_le_of_ne inf_le_left
      intro heq
      exact hnot (heq ▸ (inf_le_right : r.val ⊓ a ≤ a))
    have hlow := (le_predecessor hlt) m
    rw [StableState.rank_inf,min_eq_left hrank] at hlow
    exact (not_le_of_gt (rank_predecessor_lt hm)) hlow

/-- Sharing an actual participant forces comparability of irreducible labels. -/
theorem comparable_of_mem_support {r s : IrreducibleState P} {m : Fin n}
    (hr : m ∈ r.support) (hs : m ∈ s.support) : r ≤ s ∨ s ≤ r := by
  rcases le_total (r.val.rank m) (s.val.rank m) with h | h
  · exact Or.inl ((le_iff_rank_le hr s.val).mpr h)
  · exact Or.inr ((le_iff_rank_le hs r.val).mpr h)

theorem rank_eq_implies_eq_of_mem_support {r s : IrreducibleState P} {m : Fin n}
    (hr : m ∈ r.support) (hs : m ∈ s.support)
    (h : r.val.rank m = s.val.rank m) : r=s := by
  apply Subtype.ext
  exact le_antisymm ((le_iff_rank_le hr s.val).mpr h.le)
    ((le_iff_rank_le hs r.val).mpr h.symm.le)

/-- Every nonminimal attained rank has a unique irreducible threshold label.
The existence proof minimizes actual stable states meeting the threshold. -/
theorem exists_of_rank_increase (a b : StableState P) (m : Fin n)
    (hba : b.rank m < a.rank m) :
    ∃ r : IrreducibleState P, m ∈ r.support ∧ r.val.rank m = a.rank m := by
  classical
  obtain ⟨r,hr,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun c : StableState P ↦ a.rank m ≤ c.rank m) ⟨a,le_rfl⟩
  have hleast : ∀ c : StableState P, a.rank m ≤ c.rank m → r ≤ c := by
    intro c hc
    have hmeet : a.rank m ≤ (r ⊓ c).rank m := by
      rw [StableState.rank_inf]
      exact le_min hr hc
    exact (hmin hmeet inf_le_left).trans inf_le_right
  have hir : SupIrred r := by
    constructor
    · intro hbot
      have hle := (hbot (inf_le_left : r ⊓ b ≤ r)) m
      have hlow : (r ⊓ b).rank m ≤ b.rank m := by
        rw [StableState.rank_inf]; exact min_le_right _ _
      exact (not_le_of_gt hba) (hr.trans (hle.trans hlow))
    · intro c d heq
      have hcr : c ≤ r := heq ▸ (le_sup_left : c ≤ c ⊔ d)
      have hdr : d ≤ r := heq ▸ (le_sup_right : d ≤ c ⊔ d)
      have hmax : a.rank m ≤ max (c.rank m) (d.rank m) := by
        rw [← StableState.rank_sup,heq]
        exact hr
      rcases le_total (c.rank m) (d.rank m) with h | h
      · rw [max_eq_right h] at hmax
        exact Or.inr (le_antisymm hdr (hleast d hmax))
      · rw [max_eq_left h] at hmax
        exact Or.inl (le_antisymm hcr (hleast c hmax))
  let label : IrreducibleState P := ⟨r,hir⟩
  have hrank : r.rank m = a.rank m := le_antisymm ((hleast a le_rfl) m) hr
  refine ⟨label,?_,hrank⟩
  by_contra hm
  have heq : label.predecessor.val m = label.val.val m := by
    simpa [support,StableState.changedMen] using hm
  have hsame : label.predecessor.rank m = r.rank m := congrArg (P.manRank m) heq
  have hpred : a.rank m ≤ label.predecessor.rank m := by rw [hsame]; exact hr
  exact (not_le_of_gt label.predecessor_lt) (hleast _ hpred)

end IrreducibleState

noncomputable def irreducibleSupportHypergraph {n : Nat} (P : ProfileCode n) :
    LabeledHypergraph (Fin n) (IrreducibleState P) where
  support := IrreducibleState.support

theorem irreducibleSupport_overlap_comparable {n : Nat} (P : ProfileCode n)
    (r s : IrreducibleState P)
    (h : (irreducibleSupportHypergraph P).SupportsOverlap r s) : r ≤ s ∨ s ≤ r := by
  obtain ⟨m,hr,hs⟩ := h
  exact IrreducibleState.comparable_of_mem_support hr hs

noncomputable def participantLabels {n : Nat} (P : ProfileCode n) (m : Fin n) :
    Finset (IrreducibleState P) := by
  classical
  exact Finset.univ.filter (fun r ↦ m ∈ r.support)

def attainedRanks {n : Nat} (P : ProfileCode n) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.image (fun a : StableState P ↦ a.rank m)

def attainedPartners {n : Nat} (P : ProfileCode n) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.image (fun a : StableState P ↦ a.val m)

theorem attainedRanks_card_eq_partners {n : Nat} (P : ProfileCode n) (m : Fin n) :
    (attainedRanks P m).card = (attainedPartners P m).card := by
  have heq : attainedRanks P m = (attainedPartners P m).image (P.manRank m) := by
    simp [attainedRanks,attainedPartners,Finset.image_image,StableState.rank,Function.comp_def]
  rw [heq,Finset.card_image_of_injective _ (P.manRank m).injective]

theorem participantLabels_rank_image {n : Nat} (P : ProfileCode n) (m : Fin n)
    (best : StableState P) (hbest : ∀ a : StableState P, best.rank m ≤ a.rank m) :
    (participantLabels P m).image (fun r ↦ r.val.rank m) =
      (attainedRanks P m).erase (best.rank m) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
    have hm : m ∈ r.support := (Finset.mem_filter.mp hr).2
    have hstrict := (hbest r.predecessor).trans_lt (IrreducibleState.rank_predecessor_lt hm)
    refine Finset.mem_erase.mpr ⟨hstrict.ne.symm,?_⟩
    exact Finset.mem_image.mpr ⟨r.val,Finset.mem_univ _,rfl⟩
  · intro hk
    have hk' := Finset.mem_erase.mp hk
    obtain ⟨a,ha,hak⟩ := Finset.mem_image.mp hk'.2
    have hstrict : best.rank m < a.rank m :=
      lt_of_le_of_ne (hbest a) (fun h ↦ hk'.1 (hak.symm.trans h.symm))
    obtain ⟨r,hr,heq⟩ := IrreducibleState.exists_of_rank_increase a best m hstrict
    exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,heq.trans hak⟩

/-- Exact participant-chain length: one label for each stable partner after
the best stable partner, with no repeated rank thresholds. -/
theorem participantLabels_card_add_one {n : Nat} (P : ProfileCode n) (m : Fin n)
    [Nonempty (StableState P)] :
    (participantLabels P m).card + 1 = (attainedPartners P m).card := by
  classical
  obtain ⟨best,hb,hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (StableState P)) (fun a ↦ a.rank m) Finset.univ_nonempty
  have hbest : ∀ a : StableState P, best.rank m ≤ a.rank m := fun a ↦ hmin a (Finset.mem_univ _)
  have hinj : Set.InjOn (fun r : IrreducibleState P ↦ r.val.rank m) (participantLabels P m) := by
    intro r hr s hs heq
    exact IrreducibleState.rank_eq_implies_eq_of_mem_support
      (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2 heq
  have hcard := Finset.card_image_iff.mpr hinj
  have himage := participantLabels_rank_image P m best hbest
  have hmem : best.rank m ∈ attainedRanks P m :=
    Finset.mem_image.mpr ⟨best,Finset.mem_univ _,rfl⟩
  rw [himage,Finset.card_erase_of_mem hmem] at hcard
  have hpos := Finset.card_pos.mpr ⟨best.rank m,hmem⟩
  have hr := attainedRanks_card_eq_partners P m
  omega

theorem support_incidence_double_count {n : Nat} (P : ProfileCode n) :
    ∑ m : Fin n, (participantLabels P m).card =
      ∑ r : IrreducibleState P, r.support.card := by
  classical
  simp only [participantLabels,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp

def stablePairSet {n : Nat} (P : ProfileCode n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ p.2 ∈ attainedPartners P p.1)

theorem mem_stablePairSet {n : Nat} (P : ProfileCode n) (m w : Fin n) :
    (m,w) ∈ stablePairSet P ↔ ∃ a : MatchingCode n, Stable P a ∧ a m=w := by
  constructor
  · intro h
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).2
    exact ⟨a.val,a.property,heq⟩
  · rintro ⟨a,ha,heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,heq⟩⟩

theorem stablePairSet_card {n : Nat} (P : ProfileCode n) :
    (stablePairSet P).card = ∑ m : Fin n, (attainedPartners P m).card := by
  classical
  simp only [stablePairSet,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro m hm
  simp

/-- Exact stable-pair incidence identity for supports constructed from actual
stable matchings; no rotation incidence axiom is used. -/
theorem stablePairSet_card_eq_vertices_add_supports {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] :
    (stablePairSet P).card = n + ∑ r : IrreducibleState P, r.support.card := by
  classical
  rw [stablePairSet_card]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun m _ ↦ (participantLabels_card_add_one P m).symm)
  rw [hsum,Finset.sum_add_distrib,support_incidence_double_count]
  simp [Nat.add_comm]

end StableMatchingsE2E
