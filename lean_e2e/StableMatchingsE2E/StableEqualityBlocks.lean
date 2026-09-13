import StableMatchingsE2E.StablePairEqualityApplication

namespace StableMatchingsE2E
open scoped Classical
variable {n : Nat} {P : ProfileCode n}

noncomputable def leastStableState (P : ProfileCode n) [Nonempty (StableState P)] : StableState P :=
  (stableStateIdealEquiv P).symm ⊥

theorem ideal_leastStableState (P : ProfileCode n) [Nonempty (StableState P)] :
    stableStateIdealEquiv P (leastStableState P) = ⊥ := (stableStateIdealEquiv P).apply_symm_apply _

theorem leastStableState_le (P : ProfileCode n) [Nonempty (StableState P)] (a : StableState P) :
    leastStableState P ≤ a := by
  apply (stableStateIdealEquiv P).le_iff_le.mp
  rw [ideal_leastStableState]
  exact bot_le

theorem predecessor_eq_least_of_trivial_order (P : ProfileCode n) [Nonempty (StableState P)]
    (horder : ∀ r s : IrreducibleState P, r ≤ s → r=s) (r : IrreducibleState P) :
    r.predecessor = leastStableState P := by
  apply le_antisymm ?_ (leastStableState_le P _)
  apply (stableStateIdealEquiv P).le_iff_le.mp
  rw [ideal_leastStableState]
  intro t ht
  have htr := (mem_stableStateIdealEquiv P r.predecessor t).mp ht
  have heq : t=r := horder t r (htr.trans r.predecessor_lt.le)
  subst t
  exact False.elim ((not_le_of_gt r.predecessor_lt) htr)

theorem every_subset_antichain_of_trivial_order
    (horder : ∀ r s : IrreducibleState P, r ≤ s → r=s)
    (S : Finset (IrreducibleState P)) : LabeledHypergraph.IsAntichain (· ≤ ·) S := by
  intro r hr s hs hne
  exact ⟨fun h ↦ hne (horder r s h),fun h ↦ hne (horder s r h).symm⟩

/-- Explicit Boolean coordinates for every actual stable matching at equality. -/
noncomputable def equalityBooleanEquiv (P : ProfileCode n) (h : IndependentBinaryCover P) :
    StableState P ≃ Finset (IrreducibleState P) := by
  letI := h.1
  let forget : {S : Finset (IrreducibleState P) // LabeledHypergraph.IsAntichain (· ≤ ·) S} ≃
      Finset (IrreducibleState P) := {
    toFun := Subtype.val
    invFun S := ⟨S,every_subset_antichain_of_trivial_order h.2.2.2 S⟩
    left_inv S := Subtype.ext rfl
    right_inv S := rfl }
  exact (stableStateAntichainEquiv P).trans forget

theorem equalityBooleanEquiv_bijective (P : ProfileCode n) (h : IndependentBinaryCover P) :
    Function.Bijective (equalityBooleanEquiv P h) := (equalityBooleanEquiv P h).bijective

/-- Female block corresponding to a male support, transported through the
common least stable perfect matching. -/
noncomputable def femaleBlock (P : ProfileCode n) [Nonempty (StableState P)]
    (r : IrreducibleState P) : Finset (Fin n) := r.support.image (leastStableState P).val

theorem femaleBlock_card (P : ProfileCode n) [Nonempty (StableState P)]
    (r : IrreducibleState P) : (femaleBlock P r).card = r.support.card :=
  Finset.card_image_of_injective _ (leastStableState P).val.injective

theorem male_supports_disjoint_of_unique_cover
    (hcover : ∀ m : Fin n, ∃ r : IrreducibleState P, m ∈ r.support ∧
      ∀ s : IrreducibleState P, m ∈ s.support → s=r)
    {r s : IrreducibleState P} (hrs : r ≠ s) : Disjoint r.support s.support := by
  apply Finset.disjoint_left.mpr
  intro m hr hs
  obtain ⟨t,ht,hu⟩ := hcover m
  exact hrs ((hu r hr).trans (hu s hs).symm)

theorem femaleBlocks_disjoint (P : ProfileCode n) [Nonempty (StableState P)]
    (hcover : ∀ m : Fin n, ∃ r : IrreducibleState P, m ∈ r.support ∧
      ∀ s : IrreducibleState P, m ∈ s.support → s=r)
    {r s : IrreducibleState P} (hrs : r ≠ s) : Disjoint (femaleBlock P r) (femaleBlock P s) := by
  apply Finset.disjoint_left.mpr
  intro w hwR hwS
  obtain ⟨x,hx,hxw⟩ := Finset.mem_image.mp hwR
  obtain ⟨y,hy,hyw⟩ := Finset.mem_image.mp hwS
  have hxy := (leastStableState P).val.injective (hxw.trans hyw.symm)
  exact (Finset.disjoint_left.mp (male_supports_disjoint_of_unique_cover hcover hrs)) hx (hxy.symm ▸ hy)

theorem femaleBlocks_cover (P : ProfileCode n) [Nonempty (StableState P)]
    (hcover : ∀ m : Fin n, ∃ r : IrreducibleState P, m ∈ r.support ∧
      ∀ s : IrreducibleState P, m ∈ s.support → s=r) (w : Fin n) :
    ∃ r : IrreducibleState P, w ∈ femaleBlock P r := by
  obtain ⟨r,hr,hu⟩ := hcover ((leastStableState P).val.symm w)
  exact ⟨r,Finset.mem_image.mpr ⟨_,hr,(leastStableState P).val.apply_symm_apply w⟩⟩

theorem binary_label_swaps_base (P : ProfileCode n) [Nonempty (StableState P)]
    (horder : ∀ r s : IrreducibleState P, r ≤ s → r=s)
    (r : IrreducibleState P) {x y : Fin n} (hr : r.support={x,y}) :
    r.val.val x = (leastStableState P).val y ∧
      r.val.val y = (leastStableState P).val x := by
  have hfirst := StableState.swap_of_changedMen_pair hr
  have hr' : StableState.changedMen r.predecessor r.val = {y,x} := by
    change r.support={y,x}
    rw [hr,Finset.pair_comm]
  have hsecond := StableState.swap_of_changedMen_pair hr'
  rw [predecessor_eq_least_of_trivial_order P horder r] at hfirst hsecond
  exact ⟨hfirst,hsecond⟩

theorem mem_equalityBooleanEquiv (P : ProfileCode n) (h : IndependentBinaryCover P)
    (a : StableState P) (r : IrreducibleState P) :
    r ∈ equalityBooleanEquiv P h a ↔ r.val ≤ a := by
  letI := h.1
  change r ∈ FiniteIdealAntichain.maximals (stableStateIdealEquiv P a) ↔ r.val ≤ a
  constructor
  · intro hr
    exact (mem_stableStateIdealEquiv P a r).mp (Finset.mem_filter.mp hr).2.1
  · intro hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (mem_stableStateIdealEquiv P a r).mpr hr, ?_⟩
    intro s hs hrs
    exact (h.2.2.2 r s hrs).ge

/-- Boolean membership controls the actual partner, not just an abstract code. -/
theorem partner_of_equality_coordinate (P : ProfileCode n) (h : IndependentBinaryCover P)
    (a : StableState P) (r : IrreducibleState P) (m : Fin n) (hm : m ∈ r.support) :
    a.val m = if r ∈ equalityBooleanEquiv P h a then r.val.val m
      else (@leastStableState n P h.1).val m := by
  letI := h.1
  obtain ⟨s,hs,hu⟩ := h.2.2.1 m
  have unique : ∀ t : IrreducibleState P, m ∈ t.support → t=r := by
    intro t ht
    exact (hu t ht).trans (hu r hm).symm
  split_ifs with hc
  · have hra := (mem_equalityBooleanEquiv P h a r).mp hc
    apply (P.manRank m).injective
    change a.rank m = r.val.rank m
    apply le_antisymm ?_ (hra m)
    by_contra hn
    obtain ⟨t,ht,he⟩ := IrreducibleState.exists_of_rank_increase a r.val m (lt_of_not_ge hn)
    have ht' := unique t ht
    subst t
    exact hn he.ge
  · have hbase := leastStableState_le P a
    apply (P.manRank m).injective
    change a.rank m = (leastStableState P).rank m
    apply le_antisymm ?_ (hbase m)
    by_contra hn
    obtain ⟨t,ht,he⟩ := IrreducibleState.exists_of_rank_increase a (leastStableState P) m (lt_of_not_ge hn)
    have ht' := unique t ht
    subst t
    apply hc
    apply (mem_equalityBooleanEquiv P h a r).mpr
    exact (IrreducibleState.le_iff_rank_le hm a).mpr he.le

/-- Every subset is realized by a unique actual stable matching, with the
selected pair swapped and the unselected pair left at the common base. -/
theorem all_subsets_realize_independent_swaps (P : ProfileCode n)
    (h : IndependentBinaryCover P) (S : Finset (IrreducibleState P)) :
    ∃! a : StableState P, equalityBooleanEquiv P h a = S ∧
      ∀ (r : IrreducibleState P) (x y : Fin n), r.support = {x,y} →
        a.val x = (if r ∈ S then (@leastStableState n P h.1).val y
          else (@leastStableState n P h.1).val x) ∧
        a.val y = (if r ∈ S then (@leastStableState n P h.1).val x
          else (@leastStableState n P h.1).val y) := by
  letI := h.1
  let a := (equalityBooleanEquiv P h).symm S
  have ha : equalityBooleanEquiv P h a = S := (equalityBooleanEquiv P h).apply_symm_apply S
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro r x y hr
    have hx : x ∈ r.support := by simp [hr]
    have hy : y ∈ r.support := by simp [hr]
    have hp := binary_label_swaps_base P h.2.2.2 r hr
    constructor
    · simpa [ha, hp.1] using partner_of_equality_coordinate P h a r x hx
    · simpa [ha, hp.2] using partner_of_equality_coordinate P h a r y hy
  · intro b hb
    exact (equalityBooleanEquiv P h).injective (hb.1.trans ha.symm)

end StableMatchingsE2E
