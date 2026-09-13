import StableMatchingsE2E.ProfileCode
import StableMatchings355.FiniteJoin

namespace StableMatchingsE2E

/-- Actual stable perfect matchings, not abstract rotation configurations. -/
abbrev StableState {n : Nat} (P : ProfileCode n) := {mu : MatchingCode n // Stable P mu}

def ProfileCode.swapSides {n : Nat} (P : ProfileCode n) : ProfileCode n where
  manRank := P.womanRank
  womanRank := P.manRank

theorem stable_swapSides {n : Nat} (P : ProfileCode n) (mu : MatchingCode n)
    (hmu : Stable P mu) : Stable P.swapSides mu.symm := by
  intro w m h
  exact hmu m w ⟨h.2,h.1⟩

namespace StableState
variable {n : Nat} {P : ProfileCode n}

def rank (a : StableState P) (m : Fin n) : Fin n := P.manRank m (a.val m)

theorem ext_rank {a b : StableState P} (h : ∀ m, a.rank m = b.rank m) : a=b := by
  apply Subtype.ext
  apply Equiv.ext
  intro m
  exact (P.manRank m).injective (h m)

instance : PartialOrder (StableState P) where
  le a b := ∀ m, a.rank m ≤ b.rank m
  le_refl a m := le_refl _
  le_trans a b c hab hbc m := (hab m).trans (hbc m)
  le_antisymm a b hab hba := ext_rank (fun m ↦ le_antisymm (hab m) (hba m))

theorem le_iff (a b : StableState P) : a ≤ b ↔ ∀ m, a.rank m ≤ b.rank m := Iff.rfl

noncomputable def better (a b : StableState P) : StableState P :=
  ⟨MatchingCode.ofCore (StableMatchings355.stableMenJoin P.toCore a.val.toCore b.val.toCore
      a.property b.property),
    StableMatchings355.stableMenJoin_isStable P.toCore a.val.toCore b.val.toCore a.property b.property⟩

theorem rank_better (a b : StableState P) (m : Fin n) :
    (better a b).rank m = min (a.rank m) (b.rank m) := by
  change P.manRank m ((StableMatchings355.stableMenJoin P.toCore a.val.toCore b.val.toCore
    a.property b.property).manPartner m) = _
  rw [StableMatchings355.stableMenJoin_manPartner]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (le_of_not_gt h)).symm

noncomputable def worse (a b : StableState P) : StableState P :=
  let a' : StableState P.swapSides := ⟨a.val.symm,stable_swapSides P a.val a.property⟩
  let b' : StableState P.swapSides := ⟨b.val.symm,stable_swapSides P b.val b.property⟩
  let c := better a' b'
  ⟨c.val.symm,stable_swapSides P.swapSides c.val c.property⟩

theorem rank_worse (a b : StableState P) (m : Fin n) :
    (worse a b).rank m = max (a.rank m) (b.rank m) := by
  change P.manRank m ((StableMatchings355.stableMenJoin P.swapSides.toCore
    (MatchingCode.toCore a.val.symm) (MatchingCode.toCore b.val.symm)
    (stable_swapSides P a.val a.property) (stable_swapSides P b.val b.property)).womanPartner m) = _
  rw [StableMatchings355.stableMenJoin_womanPartner]
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (le_of_not_gt h)).symm

/-- The lattice operations are stable matchings with coordinatewise min/max
male ranks, established from the existing constructive stable-join theorem. -/
noncomputable instance : Lattice (StableState P) where
  inf := better
  sup := worse
  inf_le_left a b m := by rw [rank_better]; exact min_le_left _ _
  inf_le_right a b m := by rw [rank_better]; exact min_le_right _ _
  le_inf a b c hab hac m := by rw [rank_better]; exact le_min (hab m) (hac m)
  le_sup_left a b m := by rw [rank_worse]; exact le_max_left _ _
  le_sup_right a b m := by rw [rank_worse]; exact le_max_right _ _
  sup_le a b c hac hbc m := by rw [rank_worse]; exact max_le (hac m) (hbc m)

@[simp] theorem rank_inf (a b : StableState P) (m : Fin n) :
    (a ⊓ b).rank m = min (a.rank m) (b.rank m) := rank_better a b m

@[simp] theorem rank_sup (a b : StableState P) (m : Fin n) :
    (a ⊔ b).rank m = max (a.rank m) (b.rank m) := rank_worse a b m

noncomputable instance : DistribLattice (StableState P) where
  le_sup_inf a b c m := by
    simp only [rank_inf,rank_sup]
    exact le_of_eq (max_min_distrib_left _ _ _).symm

def changedMen (a b : StableState P) : Finset (Fin n) :=
  Finset.univ.filter (fun m ↦ a.val m ≠ b.val m)

/-- Two distinct perfect matchings cannot change only one man's partner. -/
theorem changedMen_card_ge_two {a b : StableState P} (hab : a ≠ b) :
    2 ≤ (changedMen a b).card := by
  classical
  have hex : ∃ x, a.val x ≠ b.val x := by
    by_contra h
    apply hab
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_contra hx
    exact h ⟨x,hx⟩
  obtain ⟨x,hx⟩ := hex
  let y := b.val.symm (a.val x)
  have hby : b.val y = a.val x := b.val.apply_symm_apply _
  have hyx : y ≠ x := by
    intro hy
    apply hx
    exact hby.symm.trans (congrArg b.val hy)
  have hy : a.val y ≠ b.val y := by
    intro he
    exact hyx (a.val.injective (he.trans hby))
  have hsub : ({x,y} : Finset (Fin n)) ⊆ changedMen a b := by
    intro m hm
    have hm' : m=x ∨ m=y := by simpa using hm
    rcases hm' with rfl | rfl <;> simp [changedMen,hx,hy]
  have hc := Finset.card_le_card hsub
  simpa [Ne.symm hyx] using hc

theorem rank_strict_of_le_of_changed {a b : StableState P} (hab : a ≤ b)
    {m : Fin n} (hm : m ∈ changedMen a b) : a.rank m < b.rank m := by
  have hne : a.rank m ≠ b.rank m := by
    intro h
    exact (Finset.mem_filter.mp hm).2 ((P.manRank m).injective h)
  exact lt_of_le_of_ne (hab m) hne

end StableState

/-- Canonical irreducible labels of the actual stable-matching lattice.
Identification with participant-supported rotations is a separate obligation. -/
abbrev IrreducibleState {n : Nat} (P : ProfileCode n) :=
  {a : StableState P // SupIrred a}

/-- The order-ideal representation is constructed from actual stable matchings.
Nonemptiness is explicit here; empty stable sets need no representation for counting. -/
noncomputable def stableStateIdealEquiv {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] : StableState P ≃o LowerSet (IrreducibleState P) := by
  classical
  letI : OrderBot (StableState P) := Fintype.toOrderBot (StableState P)
  exact OrderIso.lowerSetSupIrred

theorem mem_stableStateIdealEquiv {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] (a : StableState P) (r : IrreducibleState P) :
    r ∈ stableStateIdealEquiv P a ↔ r.val ≤ a := by
  rfl

theorem stableStateIdealEquiv_injective {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] : Function.Injective (stableStateIdealEquiv P) :=
  (stableStateIdealEquiv P).injective

theorem stableStateIdealEquiv_surjective {n : Nat} (P : ProfileCode n)
    [Nonempty (StableState P)] : Function.Surjective (stableStateIdealEquiv P) :=
  (stableStateIdealEquiv P).surjective

end StableMatchingsE2E
