import «CanonicalChargeCover»
import «BinomialEntropyBound»
import «EntropyCertificate»

/-!
# End-to-end deletion double count on actual stable matchings
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

/-- A fiber-cardinality formulation of the standard finite map count. -/
theorem natCard_le_natCard_mul_of_fibers {X Y : Type*}
    [Finite X] [Finite Y] (f : X → Y) (Q : Nat)
    (hfiber : ∀ y : Y, Nat.card {x : X // f x = y} ≤ Q) :
    Nat.card X ≤ Nat.card Y * Q := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Y := Fintype.ofFinite Y
  letI (y : Y) : Fintype {x : X // f x = y} := Fintype.ofFinite _
  let e : X ≃ Σ y : Y, {x : X // f x = y} :=
    { toFun := fun x ↦ ⟨f x, x, rfl⟩
      invFun := fun z ↦ z.2.1
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro z
        rcases z with ⟨y, x, hx⟩
        subst y
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  calc
    (∑ y : Y, Nat.card {x : X // f x = y}) ≤
        ∑ _y : Y, Q := Finset.sum_le_sum fun y _ ↦ hfiber y
    _ = Nat.card Y * Q := by simp [Nat.card_eq_fintype_card]

def CanonicalLowChargeSource {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :=
  {base : CodedStable P //
    (canonicalChargedMen P hstable base).card ≤ k}

def CanonicalLowChargeDeletionPair {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :=
  Σ source : CanonicalLowChargeSource P hstable k,
    ↥(maximalLengthTwoFrontier P hstable source.1).powerset

noncomputable instance canonicalLowChargeSourceFintype {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    Fintype (CanonicalLowChargeSource P hstable k) := by
  dsimp [CanonicalLowChargeSource]
  exact Fintype.ofFinite _

noncomputable instance canonicalLowChargeDeletionPairFinite {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) (k : Nat) :
    Finite (CanonicalLowChargeDeletionPair P hstable k) := by
  dsimp [CanonicalLowChargeDeletionPair]
  infer_instance

noncomputable def canonicalLowChargeDeletionImage {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty} {k : Nat}
    (x : CanonicalLowChargeDeletionPair P hstable k) : CodedStable P := by
  classical
  let D := stableRotationIdeal P hstable x.1.1
  let A : Finset (CanonicalRotation P) := x.2.1
  have hA : A ⊆ maximalLengthTwoFrontier P hstable x.1.1 :=
    Finset.mem_powerset.mp x.2.2
  have hAD : A ⊆ D := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable x.1.1 r).1
      (hA hrA)).1.1
  have hmaxA : ∀ r ∈ A, IsMaximalIn D r := by
    intro r hrA
    exact ((mem_maximalLengthTwoFrontier_iff P hstable x.1.1 r).1
      (hA hrA)).1
  have hJ : IsFinsetIdeal (D \ A) :=
    ideal_sdiff_maximal_subset D A
      (stableRotationIdeal_isIdeal P hstable x.1.1) hAD hmaxA
  exact codedStableOfIdeal P hstable (D \ A) hJ

theorem canonicalLowChargeDeletionImage_ideal {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty} {k : Nat}
    (x : CanonicalLowChargeDeletionPair P hstable k) :
    stableRotationIdeal P hstable (canonicalLowChargeDeletionImage x) =
      stableRotationIdeal P hstable x.1.1 \ x.2.1 := by
  classical
  unfold canonicalLowChargeDeletionImage
  exact stableRotationIdeal_codedStableOfIdeal_eq P hstable _ _

def CanonicalLowChargeDeletionMapFiber {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) (image : CodedStable P) :=
  {x : CanonicalLowChargeDeletionPair P hstable k //
    canonicalLowChargeDeletionImage x = image}

noncomputable def lowChargeMapFiberToCanonicalFiber {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {k : Nat} {image : CodedStable P}
    (x : CanonicalLowChargeDeletionMapFiber P hstable k image) :
    CanonicalDeletionFiberWithSourceChargeAtMost P hstable image k := by
  let source := x.1.1.1
  let A : Finset (CanonicalRotation P) := x.1.2.1
  have hA : A ⊆ maximalLengthTwoFrontier P hstable source :=
    Finset.mem_powerset.mp x.1.2.2
  have himage : stableRotationIdeal P hstable image =
      stableRotationIdeal P hstable source \ A := by
    rw [← x.2]
    exact canonicalLowChargeDeletionImage_ideal x.1
  exact ⟨
    { source := source
      deleted := A
      deleted_subset := hA
      image_ideal_eq := himage },
    x.1.1.2⟩

theorem lowChargeMapFiberToCanonicalFiber_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {k : Nat} {image : CodedStable P} :
    Function.Injective
      (lowChargeMapFiberToCanonicalFiber
        (P := P) (hstable := hstable) (k := k) (image := image)) := by
  rintro ⟨⟨⟨sx, hsx⟩, ⟨Ax, hAx⟩⟩, hix⟩
    ⟨⟨⟨sy, hsy⟩, ⟨Ay, hAy⟩⟩, hiy⟩ h
  have hsource : sx = sy := congrArg
    (fun D : CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k ↦ D.1.source) h
  subst sy
  have hdeleted : Ax = Ay := congrArg
    (fun D : CanonicalDeletionFiberWithSourceChargeAtMost
      P hstable image k ↦ D.1.deleted) h
  subst Ay
  rfl

theorem natCard_canonicalLowChargeDeletionMapFiber_le {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) (image : CodedStable P) :
    Nat.card (CanonicalLowChargeDeletionMapFiber P hstable k image) ≤
      2 ^ (n / 4) *
        (∑ i ∈ Finset.range (k + 1), n.choose i) := by
  letI : Finite (CanonicalLowChargeDeletionMapFiber P hstable k image) :=
    Finite.of_injective
      (lowChargeMapFiberToCanonicalFiber
        (P := P) (hstable := hstable) (k := k) (image := image))
      (lowChargeMapFiberToCanonicalFiber_injective
        (P := P) (hstable := hstable) (k := k) (image := image))
  exact (Nat.card_le_card_of_injective
    (lowChargeMapFiberToCanonicalFiber
      (P := P) (hstable := hstable) (k := k) (image := image))
    (lowChargeMapFiberToCanonicalFiber_injective
      (P := P) (hstable := hstable) (k := k) (image := image))).trans
    (natCard_sourceChargeDeletionFiber_le P hstable image k)

theorem lowChargeDeletionPair_count_lower {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) :
    Nat.card (CanonicalLowChargeSource P hstable k) * 2 ^ ((n - k) / 2) ≤
      Nat.card (CanonicalLowChargeDeletionPair P hstable k) := by
  classical
  letI (D : CanonicalLowChargeSource P hstable k) :
      Fintype ↥(maximalLengthTwoFrontier P hstable D.1).powerset :=
    (maximalLengthTwoFrontier P hstable D.1).powerset.fintypeCoeSort
  change Nat.card (CanonicalLowChargeSource P hstable k) *
      2 ^ ((n - k) / 2) ≤
    Nat.card (Σ D : CanonicalLowChargeSource P hstable k,
      ↥(maximalLengthTwoFrontier P hstable D.1).powerset)
  rw [Nat.card_sigma]
  calc
    Nat.card (CanonicalLowChargeSource P hstable k) *
        2 ^ ((n - k) / 2) =
        ∑ _D : CanonicalLowChargeSource P hstable k,
          2 ^ ((n - k) / 2) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ D : CanonicalLowChargeSource P hstable k,
        2 ^ (maximalLengthTwoFrontier P hstable D.1).card := by
      exact Finset.sum_le_sum fun D _ ↦
        pow_le_pow_right₀ (by omega : 1 ≤ (2 : Nat))
          (frontier_card_lower_of_charge_card_le
            P hstable D.1 k D.2)
    _ = ∑ D : CanonicalLowChargeSource P hstable k,
        Nat.card ↥(maximalLengthTwoFrontier P hstable D.1).powerset := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_powerset]

theorem lowChargeDeletionPair_count_upper {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) :
    Nat.card (CanonicalLowChargeDeletionPair P hstable k) ≤
      Nat.card (CodedStable P) *
        (2 ^ (n / 4) *
          (∑ i ∈ Finset.range (k + 1), n.choose i)) := by
  exact natCard_le_natCard_mul_of_fibers
    (canonicalLowChargeDeletionImage
      (P := P) (hstable := hstable) (k := k))
    (2 ^ (n / 4) *
      (∑ i ∈ Finset.range (k + 1), n.choose i))
    (fun image ↦
      natCard_canonicalLowChargeDeletionMapFiber_le P hstable k image)

theorem canonical_low_charge_double_count {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (k : Nat) :
    Nat.card (CanonicalLowChargeSource P hstable k) *
        2 ^ ((n - k) / 2) ≤
      Nat.card (CodedStable P) *
        (2 ^ (n / 4) *
          (∑ i ∈ Finset.range (k + 1), n.choose i)) :=
  (lowChargeDeletionPair_count_lower P hstable k).trans
    (lowChargeDeletionPair_count_upper P hstable k)

/-- The optimized deletion budget is at most half the number of subsets of
the guaranteed frontier.  The threshold `8001` includes the two one-unit
losses from the integer divisions `n/4` and `(n-k)/2`; using `4001` here
would silently ignore those rounding losses. -/
theorem optimized_boundary_budget_half {n : Nat} (hn : 8001 ≤ n) :
    2 * (2 ^ (n / 4) *
        (∑ i ∈ Finset.range ((3 * n) / 80 + 1), n.choose i)) ≤
      2 ^ ((n - (3 * n) / 80) / 2) := by
  let k := (3 * n) / 80
  let a := n / 4
  let r := (n - k) / 2
  let B := ∑ i ∈ Finset.range (k + 1), n.choose i
  have hk : 80 * k ≤ 3 * n := by
    dsimp [k]
    omega
  have hprefix :=
    choose_prefix_le_exp_binEntropy_three_eightieths
      (n := n) (k := k) hk
  have hmargin := deletion_entropy_margin_three_eightieths_quantitative
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (a : ℝ) ≤ (n : ℝ) / 4 := by
    dsimp [a]
    have hnat : 4 * (n / 4) ≤ n := by omega
    have hcast : ((4 * (n / 4) : Nat) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    nlinarith
  have hkreal : (k : ℝ) ≤ (3 : ℝ) * (n : ℝ) / 80 := by
    have hcast : ((80 * k : Nat) : ℝ) ≤ ((3 * n : Nat) : ℝ) := by
      exact_mod_cast hk
    push_cast at hcast
    nlinarith
  have hr : ((n : ℝ) - (k : ℝ)) / 2 - 1 < (r : ℝ) := by
    have hkn : k ≤ n := by omega
    have hnat : n - k < 2 * ((n - k) / 2 + 1) := by omega
    have hcast : ((n - k : Nat) : ℝ) <
        (2 * ((n - k) / 2 + 1) : Nat) := by exact_mod_cast hnat
    rw [Nat.cast_sub hkn] at hcast
    dsimp [r]
    push_cast at hcast
    nlinarith
  have hnreal : (8001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexponent :
      Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
        (r : ℝ) * Real.log 2 := by
    have hmarginN :
        (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80) <
          (n : ℝ) * (((1 : ℝ) / 4 - ((3 : ℝ) / 80) / 2) *
            Real.log 2 - ((1 : ℝ) / 4000) * Real.log 2) := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
      nlinarith
    nlinarith
  have hB : (B : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
    simpa [B] using hprefix
  have htwoA : ((2 ^ a : Nat) : ℝ) =
      Real.exp ((a : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have htwoR : ((2 ^ r : Nat) : ℝ) =
      Real.exp ((r : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hreal : ((2 * (2 ^ a * B) : Nat) : ℝ) < (2 ^ r : Nat) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, htwoA, htwoR]
    calc
      (2 : ℝ) *
          (Real.exp ((a : ℝ) * Real.log 2) * (B : ℝ)) ≤
          2 * (Real.exp ((a : ℝ) * Real.log 2) *
            Real.exp ((n : ℝ) *
              Real.binEntropy ((3 : ℝ) / 80))) := by
        gcongr
      _ = Real.exp (Real.log 2 + (a : ℝ) * Real.log 2 +
          (n : ℝ) * Real.binEntropy ((3 : ℝ) / 80)) := by
        calc
          (2 : ℝ) * (Real.exp ((a : ℝ) * Real.log 2) *
              Real.exp ((n : ℝ) * Real.binEntropy ((3 : ℝ) / 80))) =
              Real.exp (Real.log 2) *
                Real.exp ((a : ℝ) * Real.log 2) *
                Real.exp ((n : ℝ) *
                  Real.binEntropy ((3 : ℝ) / 80)) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            ring
          _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
      _ < Real.exp ((r : ℝ) * Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
  have hnat : 2 * (2 ^ a * B) < 2 ^ r := by exact_mod_cast hreal
  dsimp [a, B, r, k] at hnat ⊢
  omega

theorem canonical_low_charge_half_optimized {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (hn : 8001 ≤ n) :
    2 * Nat.card (CanonicalLowChargeSource P hstable ((3 * n) / 80)) ≤
      Nat.card (CodedStable P) := by
  let k := (3 * n) / 80
  let Q := 2 ^ (n / 4) *
    (∑ i ∈ Finset.range (k + 1), n.choose i)
  have hQ : 0 < Q := by
    dsimp [Q]
    have hsum : 0 < ∑ i ∈ Finset.range (k + 1), n.choose i := by
      apply Finset.sum_pos'
      · intro i hi
        exact Nat.zero_le _
      · refine ⟨0, by simp, ?_⟩
        simp
    exact Nat.mul_pos (pow_pos (by omega) _) hsum
  apply deletion_double_count_half
    (Nat.card (CanonicalLowChargeSource P hstable k))
    (Nat.card (CodedStable P)) Q ((n - k) / 2) hQ
  · exact canonical_low_charge_double_count P hstable k
  · simpa [Q, k] using optimized_boundary_budget_half hn

end

end StableMatchingsJointCharging
