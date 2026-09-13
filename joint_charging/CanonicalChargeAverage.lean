import «CanonicalDeletionDoubleCount»
import «GlobalChargingAssembly»

/-!
# From the actual double count to a linear average canonical charge
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

def canonicalLowChargeSourceFinset {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    Finset (CodedStable P) := by
  classical
  exact Finset.univ.filter fun base ↦
    (canonicalChargedMen P hstable base).card ≤ k

@[simp] theorem mem_canonicalLowChargeSourceFinset_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) (base : CodedStable P) :
    base ∈ canonicalLowChargeSourceFinset P hstable k ↔
      (canonicalChargedMen P hstable base).card ≤ k := by
  classical
  simp [canonicalLowChargeSourceFinset]

noncomputable def canonicalLowChargeSourceEquiv {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    CanonicalLowChargeSource P hstable k ≃
      ↥(canonicalLowChargeSourceFinset P hstable k) where
  toFun D := ⟨D.1,
    (mem_canonicalLowChargeSourceFinset_iff P hstable k D.1).2 D.2⟩
  invFun D := ⟨D.1,
    (mem_canonicalLowChargeSourceFinset_iff P hstable k D.1).1 D.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_canonicalLowChargeSourceFinset_eq_natCard {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    (canonicalLowChargeSourceFinset P hstable k).card =
      Nat.card (CanonicalLowChargeSource P hstable k) := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (canonicalLowChargeSourceEquiv P hstable k),
    Fintype.card_coe]

def canonicalTotalCharge {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) : Nat := by
  classical
  exact ∑ base : CodedStable P,
    (canonicalChargedMen P hstable base).card

theorem canonical_good_sources_pay_threshold {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    (Nat.card (CodedStable P) -
        Nat.card (CanonicalLowChargeSource P hstable k)) * (k + 1) ≤
      canonicalTotalCharge P hstable := by
  classical
  let bad := canonicalLowChargeSourceFinset P hstable k
  let good := (Finset.univ : Finset (CodedStable P)) \ bad
  have hgoodPay : ∀ base ∈ good, k + 1 ≤
      (canonicalChargedMen P hstable base).card := by
    intro base hbase
    have hnotBad : base ∉ bad := (Finset.mem_sdiff.mp hbase).2
    have hnotLe : ¬ (canonicalChargedMen P hstable base).card ≤ k := by
      intro hle
      exact hnotBad
        ((mem_canonicalLowChargeSourceFinset_iff
          P hstable k base).2 hle)
    omega
  have hgoodCard : good.card =
      Nat.card (CodedStable P) -
        Nat.card (CanonicalLowChargeSource P hstable k) := by
    have hbadSub : bad ⊆ (Finset.univ : Finset (CodedStable P)) :=
      Finset.subset_univ _
    rw [show good = (Finset.univ : Finset (CodedStable P)) \ bad by rfl,
      Finset.card_sdiff_of_subset hbadSub, Finset.card_univ,
      ← card_canonicalLowChargeSourceFinset_eq_natCard P hstable k]
    rw [Nat.card_eq_fintype_card]
  calc
    (Nat.card (CodedStable P) -
        Nat.card (CanonicalLowChargeSource P hstable k)) * (k + 1) =
        ∑ _base ∈ good, (k + 1) := by simp [hgoodCard]
    _ ≤ ∑ base ∈ good,
        (canonicalChargedMen P hstable base).card := by
      exact Finset.sum_le_sum hgoodPay
    _ ≤ ∑ base : CodedStable P,
        (canonicalChargedMen P hstable base).card := by
      exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
    _ = canonicalTotalCharge P hstable := rfl

theorem canonical_normalized_average_charge_gt_three_n_over_160
    {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (hn : 8001 ≤ n) :
    (3 : ℝ) * (n : ℝ) / 160 <
      (Nat.card (CodedStable P) : ℝ)⁻¹ *
        (canonicalTotalCharge P hstable : ℝ) := by
  let mu := Classical.choose hstable
  have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
  have hM : 0 < Nat.card (CodedStable P) := Nat.card_pos
  exact normalized_average_gt_three_n_over_160 n
    (Nat.card (CodedStable P))
    (Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)))
    (canonicalTotalCharge P hstable) hM
    (canonical_low_charge_half_optimized P hstable hn)
    (canonical_good_sources_pay_threshold
      P hstable ((3 * n) / 80))

end

end StableMatchingsJointCharging
