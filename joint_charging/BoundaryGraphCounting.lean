import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import «BoundaryMatchingCode»

/-!
# Perfect matchings in a two-matching boundary graph

This module proves the exact `2^(n/4)` counting engine without assuming a
pre-existing path/cycle decomposition.  Relative to one perfect matching,
the symmetric difference with any other is a disjoint union of cycles.  In a
maximum-degree-two ambient graph, any nonempty such cycle subgraph saturates
its entire connected component.  Hence one Boolean per component of size at
least four determines the matching.
-/

namespace StableMatchingsJointCharging

open SimpleGraph
open scoped symmDiff

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance boundaryConnectedComponentFintype
    (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofFinite _

noncomputable local instance boundaryConnectedComponentSuppFintype
    (G : SimpleGraph V) (c : G.ConnectedComponent) : Fintype c.supp :=
  Fintype.ofFinite _

def LargeBoundaryComponent (G : SimpleGraph V) :=
  {c : G.ConnectedComponent // 4 ≤ Nat.card c.supp}

noncomputable local instance largeBoundaryComponentFintype
    (G : SimpleGraph V) : Fintype (LargeBoundaryComponent G) := by
  letI : Finite (LargeBoundaryComponent G) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable def largeBoundaryComponentPickSubtype (G : SimpleGraph V)
    (c : LargeBoundaryComponent G) (i : Fin 4) : c.1.supp :=
  (Fintype.equivFin c.1.supp).symm
    ⟨i.1, lt_of_lt_of_le i.2 (by
      simpa only [← Nat.card_eq_fintype_card] using c.2)⟩

noncomputable def largeBoundaryComponentPick (G : SimpleGraph V) :
    LargeBoundaryComponent G × Fin 4 → V :=
  fun ci ↦ (largeBoundaryComponentPickSubtype G ci.1 ci.2).1

theorem largeBoundaryComponentPick_injective (G : SimpleGraph V) :
    Function.Injective (largeBoundaryComponentPick G) := by
  classical
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hcMem : largeBoundaryComponentPick G (c, i) ∈ c.1.supp :=
    (largeBoundaryComponentPickSubtype G c i).2
  have hdMem : largeBoundaryComponentPick G (d, j) ∈ d.1.supp :=
    (largeBoundaryComponentPickSubtype G d j).2
  have hcd : c.1 = d.1 := by
    have hcEq := (c.1.mem_supp_iff (largeBoundaryComponentPick G (c, i))).1 hcMem
    have hdEq := (d.1.mem_supp_iff (largeBoundaryComponentPick G (d, j))).1 hdMem
    exact hcEq.symm.trans ((congrArg G.connectedComponentMk h).trans hdEq)
  have hcsub : c = d := Subtype.ext hcd
  subst d
  have hcF : 4 ≤ Fintype.card c.1.supp := by
    simpa only [← Nat.card_eq_fintype_card] using c.2
  have hijSubtype : largeBoundaryComponentPickSubtype G c i =
      largeBoundaryComponentPickSubtype G c j := by
    apply Subtype.ext
    exact h
  have hijFin : (⟨i.1, lt_of_lt_of_le i.2 hcF⟩ :
      Fin (Fintype.card c.1.supp)) =
      ⟨j.1, lt_of_lt_of_le j.2 hcF⟩ :=
    (Fintype.equivFin c.1.supp).symm.injective hijSubtype
  have hijVal : i.1 = j.1 :=
    congrArg (fun x : Fin (Fintype.card c.1.supp) ↦ x.1) hijFin
  have hij : i = j := Fin.ext hijVal
  subst j
  rfl

theorem four_mul_card_largeBoundaryComponent_le (G : SimpleGraph V) :
    4 * Fintype.card (LargeBoundaryComponent G) ≤ Fintype.card V := by
  classical
  have h := Fintype.card_le_of_injective
    (largeBoundaryComponentPick G)
    (largeBoundaryComponentPick_injective G)
  simpa [Nat.mul_comm] using h

theorem neighborSet_eq_of_isCycles_of_le_of_degree_le_two
    {G H : SimpleGraph V} (hHG : H ≤ G) (hcyc : H.IsCycles)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {v : V} (hv : (H.neighborSet v).Nonempty) :
    H.neighborSet v = G.neighborSet v := by
  apply Set.eq_of_subset_of_ncard_le (neighborSet_mono hHG v)
  rw [hcyc hv]
  exact hdeg v

theorem isCycles_active_propagates_of_degree_le_two
    {G H : SimpleGraph V} (hHG : H ≤ G) (hcyc : H.IsCycles)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {u v : V} (hu : (H.neighborSet u).Nonempty) (huv : G.Adj u v) :
    (H.neighborSet v).Nonempty := by
  have heq := neighborSet_eq_of_isCycles_of_le_of_degree_le_two
    hHG hcyc hdeg hu
  have huvH : H.Adj u v := by
    rw [← SimpleGraph.mem_neighborSet, heq]
    exact huv
  exact ⟨u, huvH.symm⟩

theorem isCycles_saturates_connected_component
    {G H : SimpleGraph V} (hHG : H ≤ G) (hcyc : H.IsCycles)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {u v : V} (hu : (H.neighborSet u).Nonempty)
    (huvComp : G.connectedComponentMk v = G.connectedComponentMk u) :
    H.neighborSet v = G.neighborSet v := by
  have hreach : G.Reachable u v :=
    ConnectedComponent.exact huvComp.symm
  clear huvComp
  rw [reachable_iff_reflTransGen] at hreach
  have hactive : (H.neighborSet v).Nonempty := by
    induction hreach with
    | refl => exact hu
    | tail hxy hstep ih =>
        exact isCycles_active_propagates_of_degree_le_two
          hHG hcyc hdeg ih hstep
  exact neighborSet_eq_of_isCycles_of_le_of_degree_le_two
    hHG hcyc hdeg hactive

theorem isCycles_contains_ambient_edge_in_active_component
    {G H : SimpleGraph V} (hHG : H ≤ G) (hcyc : H.IsCycles)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {u a b : V} (hu : (H.neighborSet u).Nonempty)
    (haComp : G.connectedComponentMk a = G.connectedComponentMk u)
    (hab : G.Adj a b) : H.Adj a b := by
  have heq := isCycles_saturates_connected_component
    hHG hcyc hdeg hu haComp
  rw [← SimpleGraph.mem_neighborSet, heq]
  exact hab

abbrev PerfectBoundaryMatching (G : SimpleGraph V) :=
  {M : G.Subgraph // M.IsPerfectMatching}

noncomputable local instance perfectBoundaryMatchingFintype
    (G : SimpleGraph V) : Fintype (PerfectBoundaryMatching G) :=
  Fintype.ofFinite _

/-- A deliberately exact semantic hypothesis: every nonempty cycle
subgraph of `G` occupies a connected component with at least four vertices.
The two-colored canonical boundary graph discharges it from alternation and
the no-parallel theorem. -/
def HasNoShortCycleComponent (G : SimpleGraph V) : Prop :=
  ∀ (H : SimpleGraph V), H ≤ G → H.IsCycles →
    ∀ ⦃u v : V⦄, H.Adj u v →
      4 ≤ Nat.card (G.connectedComponentMk u).supp

/-- A graph presented as the union of two matchings.  The color relations
need not be disjoint; uniqueness in each color is the only property needed
for degree two and the four-vertex cycle bound. -/
structure TwoMatchingColoring (G : SimpleGraph V)
    (red blue : V → V → Prop) : Prop where
  red_symm : ∀ ⦃u v : V⦄, red u v → red v u
  blue_symm : ∀ ⦃u v : V⦄, blue u v → blue v u
  cover : ∀ ⦃u v : V⦄, G.Adj u v → red u v ∨ blue u v
  red_unique : ∀ ⦃u v w : V⦄, red u v → red u w → v = w
  blue_unique : ∀ ⦃u v w : V⦄, blue u v → blue u w → v = w

noncomputable def TwoMatchingColoring.neighborColor
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) (u : V)
    (v : G.neighborSet u) : Bool := by
  classical
  exact decide (red u v.1)

theorem TwoMatchingColoring.neighborColor_injective
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) (u : V) :
    Function.Injective (C.neighborColor u) := by
  classical
  intro v w h
  apply Subtype.ext
  have hvAdj : G.Adj u v.1 := v.2
  have hwAdj : G.Adj u w.1 := w.2
  by_cases hvr : red u v.1
  · have hvc : C.neighborColor u v = true := by
      simp [TwoMatchingColoring.neighborColor, hvr]
    have hwc : C.neighborColor u w = true := by rw [← h]; exact hvc
    have hwr : red u w.1 := by
      simpa [TwoMatchingColoring.neighborColor] using hwc
    exact C.red_unique hvr hwr
  · have hvc : C.neighborColor u v = false := by
      simp [TwoMatchingColoring.neighborColor, hvr]
    have hwc : C.neighborColor u w = false := by rw [← h]; exact hvc
    have hwr : ¬ red u w.1 := by
      simpa [TwoMatchingColoring.neighborColor] using hwc
    have hvb : blue u v.1 := (C.cover hvAdj).resolve_left hvr
    have hwb : blue u w.1 := (C.cover hwAdj).resolve_left hwr
    exact C.blue_unique hvb hwb

theorem TwoMatchingColoring.degree_le_two
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) (u : V) :
    (G.neighborSet u).ncard ≤ 2 := by
  classical
  letI : Fintype (G.neighborSet u) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective (C.neighborColor u)
    (C.neighborColor_injective u)
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    Fintype.card_bool] using h

theorem TwoMatchingColoring.no_short_cycle_component
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) :
    HasNoShortCycleComponent G := by
  classical
  intro H hHG hcyc u v huv
  have huvG : G.Adj u v := hHG huv
  obtain ⟨w, hvw, huw⟩ := hcyc.other_adj_of_adj huv
  obtain ⟨x, hux, hvx⟩ := hcyc.other_adj_of_adj huv.symm
  have huwG : G.Adj u w := hHG huw
  have hvxG : G.Adj v x := hHG hvx
  have hwx : w ≠ x := by
    intro hwxEq
    subst x
    rcases C.cover huvG with huvR | huvB
    · have huwB : blue u w := by
        rcases C.cover huwG with huwR | huwB
        · exact False.elim (hvw (C.red_unique huvR huwR))
        · exact huwB
      have hvwB : blue v w := by
        rcases C.cover hvxG with hvwR | hvwB
        · exact False.elim (hux (C.red_unique (C.red_symm huvR) hvwR))
        · exact hvwB
      exact huvG.ne (C.blue_unique (C.blue_symm huwB) (C.blue_symm hvwB))
    · have huwR : red u w := by
        rcases C.cover huwG with huwR | huwB
        · exact huwR
        · exact False.elim (hvw (C.blue_unique huvB huwB))
      have hvwR : red v w := by
        rcases C.cover hvxG with hvwR | hvwB
        · exact hvwR
        · exact False.elim (hux (C.blue_unique (C.blue_symm huvB) hvwB))
      exact huvG.ne (C.red_unique (C.red_symm huwR) (C.red_symm hvwR))
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
  let S : Finset V := {u, v, w, x}
  have hcardFour : S.card = 4 := by
    have huvne : u ≠ v := huv.ne
    have huwne : u ≠ w := huw.ne
    have hvxne : v ≠ x := hvx.ne
    simp [S, huvne, huwne, hvw, hux, hvxne, hwx]
  let embed : (↥S) → (G.connectedComponentMk u).supp := fun y ↦
    ⟨y.1, by
      have hyMem := y.2
      change y.1 ∈ ({u, v, w, x} : Finset V) at hyMem
      have hy : y.1 = u ∨ y.1 = v ∨ y.1 = w ∨ y.1 = x := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hyMem
      rcases hy with hu | hv | hw | hx
      · simpa [c, hu] using huC
      · simpa [c, hv] using hvC
      · simpa [c, hw] using hwC
      · simpa [c, hx] using hxC⟩
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

def TwoMatchingColoring.induce
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) (s : Set V) :
    TwoMatchingColoring (G.induce s)
      (fun u v ↦ red u.1 v.1) (fun u v ↦ blue u.1 v.1) where
  red_symm := by
    intro u v h
    exact C.red_symm h
  blue_symm := by
    intro u v h
    exact C.blue_symm h
  cover := by
    intro u v h
    exact C.cover h
  red_unique := by
    intro u v w huv huw
    exact Subtype.ext (C.red_unique huv huw)
  blue_unique := by
    intro u v w huv huw
    exact Subtype.ext (C.blue_unique huv huw)

noncomputable def perfectBoundaryMatchingCycleCode
    (G : SimpleGraph V) (M0 M : PerfectBoundaryMatching G) :
    LargeBoundaryComponent G → Bool := by
  classical
  exact fun c ↦ decide (∃ u v : V,
    (M.1.spanningCoe ∆ M0.1.spanningCoe).Adj u v ∧ u ∈ c.1.supp)

set_option maxHeartbeats 1200000 in
theorem perfectBoundaryMatchingCycleCode_injective
    (G : SimpleGraph V)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    (hshort : HasNoShortCycleComponent G)
    (M0 : PerfectBoundaryMatching G) :
    Function.Injective (perfectBoundaryMatchingCycleCode G M0) := by
  classical
  intro M N hcode
  apply Subtype.ext
  apply Subgraph.ext
    (M.2.2.verts_eq_univ.trans N.2.2.verts_eq_univ.symm)
  funext a b
  apply propext
  let HM := M.1.spanningCoe ∆ M0.1.spanningCoe
  let HN := N.1.spanningCoe ∆ M0.1.spanningCoe
  have hMle : HM ≤ G :=
    (symmDiff_le_sup.trans (sup_le M.1.spanningCoe_le M0.1.spanningCoe_le))
  have hNle : HN ≤ G :=
    (symmDiff_le_sup.trans (sup_le N.1.spanningCoe_le M0.1.spanningCoe_le))
  have hMcyc : HM.IsCycles := M.2.symmDiff_isCycles M0.2
  have hNcyc : HN.IsCycles := N.2.symmDiff_isCycles M0.2
  have hMN : HM.Adj a b ↔ HN.Adj a b := by
    constructor
    · intro habM
      have hlarge : 4 ≤ Nat.card (G.connectedComponentMk a).supp :=
        hshort HM hMle hMcyc habM
      let c : LargeBoundaryComponent G :=
        ⟨G.connectedComponentMk a, hlarge⟩
      have hbitM : perfectBoundaryMatchingCycleCode G M0 M c = true := by
        simp only [perfectBoundaryMatchingCycleCode, decide_eq_true_eq]
        exact ⟨a, b, habM, by simp [c]⟩
      have hbitN : perfectBoundaryMatchingCycleCode G M0 N c = true := by
        rw [← hcode]
        exact hbitM
      have hexN : ∃ u v : V, HN.Adj u v ∧ u ∈ c.1.supp := by
        simpa only [perfectBoundaryMatchingCycleCode, decide_eq_true_eq] using hbitN
      obtain ⟨u, v, huvN, huComp⟩ := hexN
      have huActive : (HN.neighborSet u).Nonempty :=
        ⟨v, by simpa [SimpleGraph.mem_neighborSet] using huvN⟩
      apply isCycles_contains_ambient_edge_in_active_component
        hNle hNcyc hdeg huActive
      · have hua : G.connectedComponentMk u = G.connectedComponentMk a := by
          simpa [c] using (c.1.mem_supp_iff u).1 huComp
        exact hua.symm
      · exact hMle habM
    · intro habN
      have hlarge : 4 ≤ Nat.card (G.connectedComponentMk a).supp :=
        hshort HN hNle hNcyc habN
      let c : LargeBoundaryComponent G :=
        ⟨G.connectedComponentMk a, hlarge⟩
      have hbitN : perfectBoundaryMatchingCycleCode G M0 N c = true := by
        simp only [perfectBoundaryMatchingCycleCode, decide_eq_true_eq]
        exact ⟨a, b, habN, by simp [c]⟩
      have hbitM : perfectBoundaryMatchingCycleCode G M0 M c = true := by
        rw [hcode]
        exact hbitN
      have hexM : ∃ u v : V, HM.Adj u v ∧ u ∈ c.1.supp := by
        simpa only [perfectBoundaryMatchingCycleCode, decide_eq_true_eq] using hbitM
      obtain ⟨u, v, huvM, huComp⟩ := hexM
      have huActive : (HM.neighborSet u).Nonempty :=
        ⟨v, by simpa [SimpleGraph.mem_neighborSet] using huvM⟩
      apply isCycles_contains_ambient_edge_in_active_component
        hMle hMcyc hdeg huActive
      · have hua : G.connectedComponentMk u = G.connectedComponentMk a := by
          simpa [c] using (c.1.mem_supp_iff u).1 huComp
        exact hua.symm
      · exact hNle habN
  have := hMN
  simp only [HM, HN, symmDiff_def, sdiff_adj, sup_adj] at this
  tauto

theorem card_perfectBoundaryMatching_le_two_pow_quarter
    (G : SimpleGraph V)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    (hshort : HasNoShortCycleComponent G) :
    Fintype.card (PerfectBoundaryMatching G) ≤
      2 ^ (Fintype.card V / 4) := by
  classical
  by_cases hempty : IsEmpty (PerfectBoundaryMatching G)
  · letI : IsEmpty (PerfectBoundaryMatching G) := hempty
    simp
  · haveI : Nonempty (PerfectBoundaryMatching G) := not_isEmpty_iff.mp hempty
    let M0 : PerfectBoundaryMatching G := Classical.choice inferInstance
    have hcode := card_le_two_pow_of_injective_cycle_code
      (perfectBoundaryMatchingCycleCode G M0)
      (perfectBoundaryMatchingCycleCode_injective G hdeg hshort M0)
    have hc := four_mul_card_largeBoundaryComponent_le G
    have hcle : Fintype.card (LargeBoundaryComponent G) ≤ Fintype.card V / 4 := by
      omega
    exact hcode.trans (pow_le_pow_right₀ (by norm_num) hcle)

theorem TwoMatchingColoring.natCard_perfectMatching_induce_le_two_pow_quarter
    {G : SimpleGraph V} {red blue : V → V → Prop}
    (C : TwoMatchingColoring G red blue) (s : Set V) :
    Nat.card (PerfectBoundaryMatching (G.induce s)) ≤
      2 ^ (Nat.card s / 4) := by
  classical
  letI : Fintype s := Fintype.ofFinite _
  let Cs := C.induce s
  have h := card_perfectBoundaryMatching_le_two_pow_quarter
    (G.induce s) (Cs.degree_le_two) (Cs.no_short_cycle_component)
  simpa only [Nat.card_eq_fintype_card] using h

end

end StableMatchingsJointCharging
