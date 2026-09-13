import StableMatchingsE2E.StablePairHypergraph

namespace StableMatchingsE2E.FiniteIdealAntichain
variable {A : Type} [Fintype A] [PartialOrder A]

noncomputable def maximals (I : LowerSet A) : Finset A := by
  classical
  exact Finset.univ.filter (fun a ↦ a ∈ I ∧ ∀ b ∈ I, a ≤ b → b ≤ a)

theorem mem_iff_below_maximal (I : LowerSet A) (a : A) :
    a ∈ I ↔ ∃ b ∈ maximals I, a ≤ b := by
  classical
  constructor
  · intro ha
    obtain ⟨b,hab,hb,hmax⟩ := exists_maximal_ge_of_wellFoundedGT (fun b ↦ b ∈ I) a ha
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hmax⟩,hab⟩
  · rintro ⟨b,hb,hab⟩
    exact I.lower hab (Finset.mem_filter.mp hb).2.1

theorem maximals_antichain (I : LowerSet A) :
    LabeledHypergraph.IsAntichain (· ≤ ·) (maximals I) := by
  classical
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  constructor
  · intro hle
    exact hab (le_antisymm hle (ha'.2 b hb'.1 hle))
  · intro hle
    exact hab (le_antisymm (hb'.2 a ha'.1 hle) hle)

theorem maximals_injective : Function.Injective (maximals (A := A)) := by
  intro I J heq
  ext a
  change a ∈ I ↔ a ∈ J
  rw [mem_iff_below_maximal,mem_iff_below_maximal,heq]

def generated (S : Finset A) : LowerSet A :=
  ⟨{a | ∃ b ∈ S, a ≤ b}, by
    intro a b hab hb
    obtain ⟨c,hc,hbc⟩ := hb
    exact ⟨c,hc,hab.trans hbc⟩⟩

theorem generated_maximals (I : LowerSet A) : generated (maximals I) = I := by
  ext a
  exact (mem_iff_below_maximal I a).symm

theorem maximals_generated (S : Finset A) (hS : LabeledHypergraph.IsAntichain (· ≤ ·) S) :
    maximals (generated S) = S := by
  classical
  ext a
  constructor
  · intro ha
    have ha' := (Finset.mem_filter.mp ha).2
    obtain ⟨b,hb,hab⟩ := ha'.1
    have hba := ha'.2 b ⟨b,hb,le_rfl⟩ hab
    exact (le_antisymm hab hba) ▸ hb
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,ha,le_rfl⟩,?_⟩
    intro b hb hab
    obtain ⟨c,hc,hbc⟩ := hb
    have hac : a=c := by
      by_contra hne
      exact (hS a ha c hc hne).1 (hab.trans hbc)
    exact hac.symm ▸ hbc

noncomputable def equiv : LowerSet A ≃
    {S : Finset A // LabeledHypergraph.IsAntichain (· ≤ ·) S} where
  toFun I := ⟨maximals I,maximals_antichain I⟩
  invFun S := generated S.val
  left_inv := generated_maximals
  right_inv S := Subtype.ext (maximals_generated S.val S.property)

end StableMatchingsE2E.FiniteIdealAntichain
