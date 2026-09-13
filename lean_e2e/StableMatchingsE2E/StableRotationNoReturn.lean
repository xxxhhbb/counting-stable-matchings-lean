import StableMatchingsE2E.StableRotationSupport
import StableMatchingsE2E.StablePairShrinking

namespace StableMatchingsE2E
namespace StableState
variable {n : Nat} {P : ProfileCode n}

theorem swap_of_changedMen_pair {a b : StableState P} {x y : Fin n}
    (hpair : changedMen a b = {x,y}) : b.val x = a.val y := by
  classical
  have hx : a.val x ≠ b.val x := by
    have hm : x ∈ changedMen a b := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  let k := a.val.symm (b.val x)
  have hak : a.val k = b.val x := a.val.apply_symm_apply _
  have hkx : k ≠ x := by
    intro he
    exact hx ((congrArg a.val he).symm.trans hak)
  have hkchanged : k ∈ changedMen a b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro he
    exact hkx (b.val.injective (he.symm.trans hak))
  have hky : k=y := by simpa [hpair,hkx] using hkchanged
  exact hak.symm.trans (congrArg a.val hky)

end StableState
namespace IrreducibleState
variable {n : Nat} {P : ProfileCode n}

theorem rank_predecessor_eq_of_no_between {r s : IrreducibleState P} {m : Fin n}
    (hrs : r < s) (hr : m ∈ r.support)
    (hgap : ∀ t : IrreducibleState P, m ∈ t.support → ¬(r < t ∧ t < s)) :
    s.predecessor.rank m = r.val.rank m := by
  have hrpred : r.val ≤ s.predecessor := le_predecessor hrs
  apply le_antisymm
  · by_contra hn
    have hinc : r.val.rank m < s.predecessor.rank m := lt_of_not_ge hn
    obtain ⟨t,ht,htrank⟩ := exists_of_rank_increase s.predecessor r.val m hinc
    have htpred : t.val ≤ s.predecessor := (le_iff_rank_le ht _).mpr htrank.le
    have hrt : r.val ≤ t.val := (le_iff_rank_le hr _).mpr (by rw [htrank]; exact hinc.le)
    have hne : r ≠ t := by
      intro he
      have heq : r.val.rank m = t.val.rank m := congrArg (fun u : IrreducibleState P ↦ u.val.rank m) he
      rw [htrank] at heq
      exact hinc.ne heq
    exact hgap t ht ⟨lt_of_le_of_ne hrt hne,htpred.trans_lt s.predecessor_lt⟩
  · exact hrpred m

/-- Two consecutive binary changes on the same two men would swap back to
an earlier partner, contradicting strict increase of the actual male rank. -/
theorem no_consecutive_binary_same_support {r s : IrreducibleState P} {x y : Fin n}
    (hrs : r < s) (hr : r.support = {x,y}) (hs : s.support = {x,y})
    (hgap : ∀ t : IrreducibleState P, (x ∈ t.support ∨ y ∈ t.support) →
      ¬(r < t ∧ t < s)) : False := by
  have hrx : x ∈ r.support := by rw [hr]; simp
  have hry : y ∈ r.support := by rw [hr]; simp
  have hmidY := rank_predecessor_eq_of_no_between hrs hry (fun t ht ↦ hgap t (Or.inr ht))
  have hpartnerY : s.predecessor.val y = r.val.val y := (P.manRank y).injective hmidY
  have hswapS : s.val.val x = s.predecessor.val y := StableState.swap_of_changedMen_pair hs
  have hr' : StableState.changedMen r.predecessor r.val = {y,x} := by
    change r.support = {y,x}
    rw [hr,Finset.pair_comm]
  have hswapR : r.val.val y = r.predecessor.val x := StableState.swap_of_changedMen_pair hr'
  have hreturn : s.val.rank x = r.predecessor.rank x :=
    congrArg (P.manRank x) (hswapS.trans (hpartnerY.trans hswapR))
  have hstrict := (rank_predecessor_lt hrx).trans_le (hrs.le x)
  exact hstrict.ne hreturn.symm

end IrreducibleState

/-- An isolated support on two men has at most one irreducible label.
This excludes doubles, triples, and all higher multiplicities at once. -/
theorem isolated_binary_support_card_le_one {n : Nat} (P : ProfileCode n)
    (S : Finset (Fin n)) (hS : S.card = 2)
    (hiso : ∀ t : IrreducibleState P, ¬Disjoint t.support S → t.support = S) :
    (Finset.univ.filter (fun t : IrreducibleState P ↦ t.support = S)).card ≤ 1 := by
  classical
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hS
  have hbad : ∀ r s : IrreducibleState P, r.support = {x,y} → s.support = {x,y} →
      r < s → False := by
    intro r s hr hs hrs
    obtain ⟨u,hu,hmin⟩ := exists_minimal_of_wellFoundedLT
      (fun t : IrreducibleState P ↦ r < t ∧ t.support = {x,y}) ⟨s,hrs,hs⟩
    apply IrreducibleState.no_consecutive_binary_same_support hu.1 hr hu.2
    intro t ht hbetween
    have hmeet : ¬Disjoint t.support ({x,y} : Finset (Fin n)) := by
      rcases ht with hx | hy
      · exact Finset.not_disjoint_iff.mpr ⟨x,hx,by simp⟩
      · exact Finset.not_disjoint_iff.mpr ⟨y,hy,by simp⟩
    have htu := hmin ⟨hbetween.1,hiso t hmeet⟩ hbetween.2.le
    exact (not_le_of_gt hbetween.2) htu
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  by_contra hne
  have hrx : x ∈ r.support := by rw [hr']; simp
  have hsx : x ∈ s.support := by rw [hs']; simp
  rcases IrreducibleState.comparable_of_mem_support hrx hsx with h | h
  · exact hbad r s hr' hs' (lt_of_le_of_ne h hne)
  · exact hbad s r hs' hr' (lt_of_le_of_ne h (Ne.symm hne))

theorem irreducibleSupport_no_isolated_double {n : Nat} (P : ProfileCode n)
    (S : Finset (Fin n)) : ¬(irreducibleSupportHypergraph P).IsIsolatedDouble S := by
  intro h
  have hle := isolated_binary_support_card_le_one P S h.1 h.2.1
  have heq := h.2.2
  change (Finset.univ.filter (fun t : IrreducibleState P ↦ t.support = S)).card = 2 at heq
  omega

end StableMatchingsE2E
