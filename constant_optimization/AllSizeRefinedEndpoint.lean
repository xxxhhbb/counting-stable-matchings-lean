import «CanonicalUniformPaymentGlobal»
import StableMatchingsE2E.Replication
import StableMatchingsE2E.FixedEdges

/-!
# All-size refined endpoint

The charging theorem directly proves the `3.3248` endpoint above its finite
threshold.  Replication removes that threshold: if a profile of size `n`
violated the bound, `850001` independent copies would violate the direct
large-size theorem.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

/-- The all-size `3.3248` theorem, including the replication step. -/
theorem SM_lt_2078_div_625_pow_all_sizes
    (n : Nat) (hn : 1 ≤ n) :
    (SM n : ℝ) < ((2078 : ℝ) / 625) ^ n := by
  let t : Nat := 850001
  letI : NeZero t := ⟨by norm_num [t]⟩
  have hthreshold : 850001 ≤ t * n := by
    dsimp [t]
    omega
  have hlarge := SM_lt_2078_div_625_pow (t * n) hthreshold
  have hsuperNat : SM n ^ t ≤ SM (t * n) :=
    SM_pow_le_SM_mul n t
  have hsuperReal : (SM n : ℝ) ^ t ≤ (SM (t * n) : ℝ) := by
    exact_mod_cast hsuperNat
  have hpow : (SM n : ℝ) ^ t <
      (((2078 : ℝ) / 625) ^ n) ^ t := by
    calc
      (SM n : ℝ) ^ t ≤ (SM (t * n) : ℝ) := hsuperReal
      _ < ((2078 : ℝ) / 625) ^ (t * n) := hlarge
      _ = (((2078 : ℝ) / 625) ^ n) ^ t := by
        rw [Nat.mul_comm t n, pow_mul]
  by_contra hnot
  have hle : ((2078 : ℝ) / 625) ^ n ≤ (SM n : ℝ) :=
    le_of_not_gt hnot
  have hpows : (((2078 : ℝ) / 625) ^ n) ^ t ≤ (SM n : ℝ) ^ t := by
    gcongr
  exact (not_lt_of_ge hpows) hpow

/-- If fewer than all men are prescribed, the number of stable completions
is strictly below `3.3248^(n-|A|)`.  The prescription is represented by its
stable base completion on `A`. -/
theorem fixedFiber_card_lt_2078_div_625_pow {n : Nat}
    (P : ProfileCode n) (base : MatchingCode n) (A : Finset (Fin n))
    (hfree : A.card < n) :
    ((fixedFiber P base A).card : ℝ) <
      ((2078 : ℝ) / 625) ^ (n - A.card) := by
  have hleNat : (fixedFiber P base A).card ≤ SM (n - A.card) :=
    fixedFiber_card_le_SM P base A
  have hleReal : ((fixedFiber P base A).card : ℝ) ≤
      (SM (n - A.card) : ℝ) := by
    exact_mod_cast hleNat
  calc
    ((fixedFiber P base A).card : ℝ) ≤ (SM (n - A.card) : ℝ) := hleReal
    _ < ((2078 : ℝ) / 625) ^ (n - A.card) :=
      SM_lt_2078_div_625_pow_all_sizes (n - A.card)
        (Nat.sub_pos_iff_lt.mpr hfree)

/-- If every man is prescribed by a stable base matching, that base is the
unique compatible stable completion. -/
theorem fixedFiber_card_eq_one_of_all_fixed {n : Nat}
    (P : ProfileCode n) (base : MatchingCode n) (A : Finset (Fin n))
    (hbase : Stable P base) (hall : A.card = n) :
    (fixedFiber P base A).card = 1 :=
  fixedFiber_card_eq_one_of_card_eq P base A hbase hall

/-- Real-valued bound for an explicit compatible prescription. -/
theorem prescribedFiber_card_lt_2078_div_625_pow {n : Nat}
    (P : ProfileCode n) (A : Finset (Fin n)) (eta : ↥A → Fin n)
    (base : MatchingCode n) (hbaseExt : ExtendsPrescription A eta base)
    (hfree : A.card < n) :
    ((prescribedFiber P A eta).card : ℝ) <
      ((2078 : ℝ) / 625) ^ (n - A.card) := by
  rw [prescribedFiber_eq_fixedFiber_of_extends P A eta base hbaseExt]
  exact fixedFiber_card_lt_2078_div_625_pow P base A hfree

/-- A compatible prescription fixing all men has one stable completion. -/
theorem prescribedFiber_card_eq_one_of_all_fixed {n : Nat}
    (P : ProfileCode n) (A : Finset (Fin n)) (eta : ↥A → Fin n)
    (base : MatchingCode n) (hbase : Stable P base)
    (hbaseExt : ExtendsPrescription A eta base) (hall : A.card = n) :
    (prescribedFiber P A eta).card = 1 :=
  prescribedFiber_card_eq_one_of_card_eq P A eta base hbase hbaseExt hall

end

end StableMatchingsJointCharging

open StableMatchingsJointCharging

#check SM_lt_2078_div_625_pow_all_sizes
#print axioms SM_lt_2078_div_625_pow_all_sizes
#check fixedFiber_card_lt_2078_div_625_pow
#print axioms fixedFiber_card_lt_2078_div_625_pow
#check fixedFiber_card_eq_one_of_all_fixed
#print axioms fixedFiber_card_eq_one_of_all_fixed
#check prescribedFiber_card_lt_2078_div_625_pow
#print axioms prescribedFiber_card_lt_2078_div_625_pow
#check prescribedFiber_card_eq_one_of_all_fixed
#print axioms prescribedFiber_card_eq_one_of_all_fixed
