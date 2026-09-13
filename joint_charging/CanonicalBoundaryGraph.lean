import «CanonicalBoundaryBridge»
import «BoundaryGraphCounting»

/-!
# The actual two-coloured boundary graph of a stable-marriage profile

Vertices are the original men.  Edges are the two-man canonical rotations
which are maximal in, or minimal outside, the selected stable ideal.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E SimpleGraph

noncomputable section

def canonicalInAdj {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P)
    (u v : Fin n) : Prop :=
  ∃ r ∈ maximalLengthTwoFrontier P hstable base,
    canonicalRotationMen P hstable r = ({u, v} : Finset (Fin n))

def canonicalOutAdj {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P)
    (u v : Fin n) : Prop :=
  ∃ r ∈ minimalLengthTwoOutsideFrontier P hstable base,
    canonicalRotationMen P hstable r = ({u, v} : Finset (Fin n))

theorem canonicalInAdj_comm {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P)
    (u v : Fin n) :
    canonicalInAdj P hstable base u v ↔
      canonicalInAdj P hstable base v u := by
  constructor <;> rintro ⟨r, hr, hpair⟩ <;>
    exact ⟨r, hr, by simpa [Finset.pair_comm] using hpair⟩

theorem canonicalOutAdj_comm {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P)
    (u v : Fin n) :
    canonicalOutAdj P hstable base u v ↔
      canonicalOutAdj P hstable base v u := by
  constructor <;> rintro ⟨r, hr, hpair⟩ <;>
    exact ⟨r, hr, by simpa [Finset.pair_comm] using hpair⟩

def canonicalBoundaryGraph {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (base : CodedStable P) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    (canonicalInAdj P hstable base u v ∨
      canonicalOutAdj P hstable base u v)
  symm := by
    constructor
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hin | hout
    · exact Or.inl ((canonicalInAdj_comm P hstable base u v).1 hin)
    · exact Or.inr ((canonicalOutAdj_comm P hstable base u v).1 hout)
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

@[simp] theorem canonicalBoundaryGraph_adj_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u v : Fin n) :
    (canonicalBoundaryGraph P hstable base).Adj u v ↔
      u ≠ v ∧ (canonicalInAdj P hstable base u v ∨
        canonicalOutAdj P hstable base u v) :=
  Iff.rfl

theorem canonicalInAdj_neighbor_unique {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u : Fin n) {v w : Fin n}
    (huv : canonicalInAdj P hstable base u v)
    (huw : canonicalInAdj P hstable base u w) : v = w := by
  obtain ⟨r, hr, hrpair⟩ := huv
  obtain ⟨s, hs, hspair⟩ := huw
  have hrInfo := (mem_maximalLengthTwoFrontier_iff P hstable base r).1 hr
  have hsInfo := (mem_maximalLengthTwoFrontier_iff P hstable base s).1 hs
  have hru : canonicalRotationInvolvesMan P hstable u r :=
    (mem_canonicalRotationMen_iff P hstable r u).1 (by simp [hrpair])
  have hsu : canonicalRotationInvolvesMan P hstable u s :=
    (mem_canonicalRotationMen_iff P hstable s u).1 (by simp [hspair])
  have hrs : r = s := canonical_maximal_involving_unique
    P hstable base u hru hsu hrInfo.1 hsInfo.1
  subst s
  have hpairs : ({u, v} : Finset (Fin n)) = {u, w} :=
    hrpair.symm.trans hspair
  by_cases hvu : v = u
  · subst v
    have hcard := hrInfo.2
    simp [canonicalLengthTwo, hrpair] at hcard
  · have hv : v ∈ ({u, w} : Finset (Fin n)) := by
      rw [← hpairs]
      simp
    simpa [hvu] using hv

theorem canonicalOutAdj_neighbor_unique {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u : Fin n) {v w : Fin n}
    (huv : canonicalOutAdj P hstable base u v)
    (huw : canonicalOutAdj P hstable base u w) : v = w := by
  obtain ⟨r, hr, hrpair⟩ := huv
  obtain ⟨s, hs, hspair⟩ := huw
  have hrInfo := (mem_minimalLengthTwoOutsideFrontier_iff P hstable base r).1 hr
  have hsInfo := (mem_minimalLengthTwoOutsideFrontier_iff P hstable base s).1 hs
  have hru : canonicalRotationInvolvesMan P hstable u r :=
    (mem_canonicalRotationMen_iff P hstable r u).1 (by simp [hrpair])
  have hsu : canonicalRotationInvolvesMan P hstable u s :=
    (mem_canonicalRotationMen_iff P hstable s u).1 (by simp [hspair])
  have hrs : r = s := canonical_minimal_outside_involving_unique
    P hstable base u hru hsu hrInfo.1 hsInfo.1
  subst s
  have hpairs : ({u, v} : Finset (Fin n)) = {u, w} :=
    hrpair.symm.trans hspair
  by_cases hvu : v = u
  · subst v
    have hcard := hrInfo.2
    simp [canonicalLengthTwo, hrpair] at hcard
  · have hv : v ∈ ({u, w} : Finset (Fin n)) := by
      rw [← hpairs]
      simp
    simpa [hvu] using hv

theorem canonicalInAdj_not_canonicalOutAdj {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) {u v : Fin n}
    (hin : canonicalInAdj P hstable base u v) :
    ¬ canonicalOutAdj P hstable base u v := by
  rintro ⟨s, hs, hspair⟩
  obtain ⟨r, hr, hrpair⟩ := hin
  have hrInfo := (mem_maximalLengthTwoFrontier_iff P hstable base r).1 hr
  have hsInfo := (mem_minimalLengthTwoOutsideFrontier_iff P hstable base s).1 hs
  exact canonical_boundary_lengthTwo_no_parallel
    P hstable base hrInfo.1 hsInfo.1 hrInfo.2 hsInfo.2
    (hrpair.trans hspair.symm)

noncomputable def canonicalBoundaryNeighborColor {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u : Fin n)
    (v : (canonicalBoundaryGraph P hstable base).neighborSet u) : Bool := by
  classical
  exact decide (canonicalOutAdj P hstable base u v.1)

theorem canonicalBoundaryNeighborColor_injective {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u : Fin n) :
    Function.Injective (canonicalBoundaryNeighborColor P hstable base u) := by
  classical
  intro v w hcolor
  apply Subtype.ext
  have hvAdj : (canonicalBoundaryGraph P hstable base).Adj u v.1 := v.2
  have hwAdj : (canonicalBoundaryGraph P hstable base).Adj u w.1 := w.2
  rcases hvAdj.2 with hvIn | hvOut
  · have hvNotOut := canonicalInAdj_not_canonicalOutAdj
      P hstable base hvIn
    have hvColor : canonicalBoundaryNeighborColor P hstable base u v = false := by
      simp [canonicalBoundaryNeighborColor, hvNotOut]
    have hwColor : canonicalBoundaryNeighborColor P hstable base u w = false := by
      rw [← hcolor]
      exact hvColor
    have hwNotOut : ¬ canonicalOutAdj P hstable base u w.1 := by
      simpa [canonicalBoundaryNeighborColor] using hwColor
    have hwIn : canonicalInAdj P hstable base u w.1 := hwAdj.2.resolve_right hwNotOut
    exact canonicalInAdj_neighbor_unique P hstable base u hvIn hwIn
  · have hvColor : canonicalBoundaryNeighborColor P hstable base u v = true := by
      simp [canonicalBoundaryNeighborColor, hvOut]
    have hwColor : canonicalBoundaryNeighborColor P hstable base u w = true := by
      rw [← hcolor]
      exact hvColor
    have hwOut : canonicalOutAdj P hstable base u w.1 := by
      simpa [canonicalBoundaryNeighborColor] using hwColor
    exact canonicalOutAdj_neighbor_unique P hstable base u hvOut hwOut

def canonicalBoundaryTwoMatchingColoring {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    TwoMatchingColoring (canonicalBoundaryGraph P hstable base)
      (canonicalInAdj P hstable base) (canonicalOutAdj P hstable base) where
  red_symm := by
    intro u v h
    exact (canonicalInAdj_comm P hstable base u v).1 h
  blue_symm := by
    intro u v h
    exact (canonicalOutAdj_comm P hstable base u v).1 h
  cover := by
    intro u v h
    exact h.2
  red_unique := by
    intro u v w h₁ h₂
    exact canonicalInAdj_neighbor_unique P hstable base u h₁ h₂
  blue_unique := by
    intro u v w h₁ h₂
    exact canonicalOutAdj_neighbor_unique P hstable base u h₁ h₂

theorem canonicalBoundaryGraph_degree_le_two {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (u : Fin n) :
    ((canonicalBoundaryGraph P hstable base).neighborSet u).ncard ≤ 2 := by
  classical
  letI : Fintype ((canonicalBoundaryGraph P hstable base).neighborSet u) :=
    Fintype.ofFinite _
  have h := Fintype.card_le_of_injective
    (canonicalBoundaryNeighborColor P hstable base u)
    (canonicalBoundaryNeighborColor_injective P hstable base u)
  simpa using h

theorem canonicalBoundaryGraph_no_short_cycle_component {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    HasNoShortCycleComponent (canonicalBoundaryGraph P hstable base) := by
  classical
  let G := canonicalBoundaryGraph P hstable base
  change HasNoShortCycleComponent G
  intro H hHG hcyc u v huv
  have huvG : G.Adj u v := hHG huv
  obtain ⟨w, hvw, huw⟩ := hcyc.other_adj_of_adj huv
  obtain ⟨x, hux, hvx⟩ := hcyc.other_adj_of_adj huv.symm
  have huwG : G.Adj u w := hHG huw
  have hvxG : G.Adj v x := hHG hvx
  have hwx : w ≠ x := by
    intro hwxEq
    subst x
    rcases huvG.2 with huvIn | huvOut
    · have huwOut : canonicalOutAdj P hstable base u w := by
        rcases huwG.2 with huwIn | huwOut
        · exact False.elim (hvw (canonicalInAdj_neighbor_unique
            P hstable base u huvIn huwIn))
        · exact huwOut
      have hvwOut : canonicalOutAdj P hstable base v w := by
        rcases hvxG.2 with hvwIn | hvwOut
        · have huvIn' := (canonicalInAdj_comm P hstable base u v).1 huvIn
          exact False.elim (hux (canonicalInAdj_neighbor_unique
            P hstable base v huvIn' hvwIn))
        · exact hvwOut
      have hwuOut := (canonicalOutAdj_comm P hstable base u w).1 huwOut
      have hwvOut := (canonicalOutAdj_comm P hstable base v w).1 hvwOut
      exact huvG.1 (canonicalOutAdj_neighbor_unique
        P hstable base w hwuOut hwvOut)
    · have huwIn : canonicalInAdj P hstable base u w := by
        rcases huwG.2 with huwIn | huwOut
        · exact huwIn
        · exact False.elim (hvw (canonicalOutAdj_neighbor_unique
            P hstable base u huvOut huwOut))
      have hvwIn : canonicalInAdj P hstable base v w := by
        rcases hvxG.2 with hvwIn | hvwOut
        · exact hvwIn
        · have huvOut' := (canonicalOutAdj_comm P hstable base u v).1 huvOut
          exact False.elim (hux (canonicalOutAdj_neighbor_unique
            P hstable base v huvOut' hvwOut))
      have hwuIn := (canonicalInAdj_comm P hstable base u w).1 huwIn
      have hwvIn := (canonicalInAdj_comm P hstable base v w).1 hvwIn
      exact huvG.1 (canonicalInAdj_neighbor_unique
        P hstable base w hwuIn hwvIn)
  let c := G.connectedComponentMk u
  have huC : u ∈ c.supp := by simp [c]
  have hvC : v ∈ c.supp := by
    rw [c.mem_supp_iff]
    exact (ConnectedComponent.sound huvG.reachable).symm
  have hwC : w ∈ c.supp := by
    rw [c.mem_supp_iff]
    exact (ConnectedComponent.sound huwG.reachable).symm
  have hxC : x ∈ c.supp := by
    rw [c.mem_supp_iff]
    exact (ConnectedComponent.sound
      (huvG.reachable.trans hvxG.reachable)).symm
  have hsub : ({u, v, w, x} : Finset (Fin n)) ⊆ c.supp.toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · simpa using huC
    · simpa using hvC
    · simpa using hwC
    · simpa using hxC
  have hcardFour : ({u, v, w, x} : Finset (Fin n)).card = 4 := by
    have huvne : u ≠ v := huv.ne
    have huwne : u ≠ w := huw.ne
    have hvxne : v ≠ x := hvx.ne
    simp [huvne, huwne, hvw, hux, hvxne, hwx]
  let S : Finset (Fin n) := {u, v, w, x}
  let embed : (↥S) → (G.connectedComponentMk u).supp := fun y ↦
    ⟨y.1, by
      have hy : y.1 ∈ c.supp.toFinset := hsub y.2
      simpa [c] using hy⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    have hv : a.1 = b.1 := congrArg
      (fun z : (G.connectedComponentMk u).supp ↦ z.1) hab
    exact Subtype.ext hv
  have hle := Fintype.card_le_of_injective embed hinj
  have hScard : Fintype.card ↥S = 4 := by
    rw [Fintype.card_coe]
    exact hcardFour
  rw [hScard] at hle
  have heq : Fintype.card (G.connectedComponentMk u).supp =
      Nat.card (G.connectedComponentMk u).supp :=
    (Nat.card_eq_fintype_card).symm
  exact hle.trans_eq heq

noncomputable local instance canonicalBoundaryPerfectMatchingFintype {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    Fintype (PerfectBoundaryMatching (canonicalBoundaryGraph P hstable base)) := by
  letI : Finite (PerfectBoundaryMatching
      (canonicalBoundaryGraph P hstable base)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

theorem canonicalBoundaryGraph_perfectMatching_bound {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) :
    Fintype.card (PerfectBoundaryMatching
      (canonicalBoundaryGraph P hstable base)) ≤ 2 ^ (n / 4) := by
  simpa using card_perfectBoundaryMatching_le_two_pow_quarter
    (canonicalBoundaryGraph P hstable base)
    (canonicalBoundaryGraph_degree_le_two P hstable base)
    (canonicalBoundaryGraph_no_short_cycle_component P hstable base)

/-- Exact fixed-unmatched-set form used by the deletion fiber count.  The
remaining vertices carry an induced boundary graph, and its perfect
matchings still have at most `2^(n/4)` possibilities. -/
theorem canonicalBoundaryGraph_induced_perfectMatching_bound {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (S : Set (Fin n)) :
    Nat.card (PerfectBoundaryMatching
      ((canonicalBoundaryGraph P hstable base).induce S)) ≤ 2 ^ (n / 4) := by
  have h := TwoMatchingColoring.natCard_perfectMatching_induce_le_two_pow_quarter
    (canonicalBoundaryTwoMatchingColoring P hstable base) S
  have hcard : Nat.card S ≤ n := by
    simpa using Nat.card_le_card_of_injective
      (fun x : S ↦ x.1) Subtype.val_injective
  have hdiv : Nat.card S / 4 ≤ n / 4 := by omega
  exact h.trans (pow_le_pow_right₀ (by norm_num) hdiv)

end

end StableMatchingsJointCharging
