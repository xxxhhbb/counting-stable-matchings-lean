import StableMatchingsE2E.GeometricDomination
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy

noncomputable section

attribute [local instance] Classical.propDecidable

/-! This module closes the infinite-dummy coupling.  It deliberately works
on one product space: the finite genuine marker block and both infinite
dummy tails are coordinates of the same sample. -/

abbrev BernoulliBitMeasure (x : I) : Measure Bool := Ber(true, false, x)

abbrev BernoulliSequenceMeasure (x : I) : Measure (Nat → Bool) :=
  Measure.infinitePi (fun _ : Nat => BernoulliBitMeasure x)

instance bernoulliSequenceMeasure_isProbability (x : I) :
    IsProbabilityMeasure (BernoulliSequenceMeasure x) := inferInstance

def firstSuccess (b : Nat → Bool) : Nat :=
  if h : ∃ k, b k = true then Nat.find h else 0

def hasSuccess (b : Nat → Bool) : Prop := ∃ k, b k = true

theorem firstSuccess_eq_of_first (b : Nat → Bool) (k : Nat)
    (hk : b k = true) (hbefore : ∀ i < k, b i = false) :
    firstSuccess b = k := by
  unfold firstSuccess
  rw [dif_pos ⟨k, hk⟩]
  exact (Nat.find_eq_iff ⟨k, hk⟩).mpr
    ⟨hk, fun m hm => by simp [hbefore m hm]⟩

theorem firstSuccess_spec (b : Nat → Bool) (h : hasSuccess b) :
    b (firstSuccess b) = true := by
  simp only [firstSuccess, dif_pos (show ∃ k, b k = true from h)]
  exact Nat.find_spec h

theorem firstSuccess_before (b : Nat → Bool) (h : hasSuccess b)
    {i : Nat} (hi : i < firstSuccess b) : b i = false := by
  simp only [firstSuccess, dif_pos (show ∃ k, b k = true from h)] at hi
  have hn := Nat.find_min h hi
  cases hb : b i <;> simp_all

def successEvent (k : Nat) : Set (Nat → Bool) := {b | b k = true}

theorem measurableSet_successEvent (k : Nat) : MeasurableSet (successEvent k) := by
  exact measurableSet_singleton true |>.preimage (measurable_pi_apply k)

theorem bernoulliSequenceMeasure_successEvent (x : I) (k : Nat) :
    BernoulliSequenceMeasure x (successEvent k) =
      (unitInterval.toNNReal x : ENNReal) := by
  rw [show successEvent k = (fun b : Nat → Bool => b k) ⁻¹' {true} by rfl]
  rw [← Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton true)]
  rw [Measure.infinitePi_map_eval]
  simp [BernoulliBitMeasure]

theorem iIndepSet_successEvent (x : I) :
    iIndepSet successEvent (BernoulliSequenceMeasure x) := by
  apply (iIndepSet_iff_meas_biInter measurableSet_successEvent).2
  intro s
  have hi : iIndepFun (fun k (b : Nat → Bool) => b k)
      (BernoulliSequenceMeasure x) :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  exact hi.meas_biInter (fun i _ => by
    apply MeasurableSpace.measurableSet_comap.mpr
    exact ⟨{true}, measurableSet_singleton true, rfl⟩)

theorem tsum_successEvent_eq_top {x : I} (hx : x ≠ 0) :
    ∑' k : Nat, BernoulliSequenceMeasure x (successEvent k) = ⊤ := by
  simp_rw [bernoulliSequenceMeasure_successEvent]
  rw [ENNReal.tsum_const]
  have hc : ENat.card Nat = ⊤ := ENat.card_eq_top.mpr inferInstance
  rw [hc]
  simp only [ENat.toENNReal_top]
  rw [ENNReal.top_mul]
  intro hz
  apply hx
  apply Subtype.ext
  have hz' : unitInterval.toNNReal x = 0 := ENNReal.coe_eq_zero.mp hz
  simpa using congrArg (fun y : NNReal => (y : Real)) hz'

theorem measure_limsup_successEvent_eq_one {x : I} (hx : x ≠ 0) :
    BernoulliSequenceMeasure x (limsup successEvent atTop) = 1 := by
  exact measure_limsup_eq_one measurableSet_successEvent
    (iIndepSet_successEvent x) (tsum_successEvent_eq_top hx)

theorem limsup_successEvent_subset_hasSuccess :
    limsup successEvent atTop ⊆ {b | hasSuccess b} := by
  intro b hb
  rw [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq] at hb
  exact hb.nonempty

theorem ae_hasSuccess {x : I} (hx : x ≠ 0) :
    ∀ᵐ b ∂(BernoulliSequenceMeasure x), hasSuccess b := by
  have hle : BernoulliSequenceMeasure x (limsup successEvent atTop) ≤
      BernoulliSequenceMeasure x {b | hasSuccess b} :=
    measure_mono limsup_successEvent_subset_hasSuccess
  have hmeasure : BernoulliSequenceMeasure x {b | hasSuccess b} = 1 := by
    apply le_antisymm (prob_le_one)
    simpa [measure_limsup_successEvent_eq_one hx] using hle
  have hm : MeasurableSet {b | hasSuccess b} := by
    rw [show {b | hasSuccess b} = ⋃ k, successEvent k by
      ext b
      simp [hasSuccess, successEvent]]
    exact MeasurableSet.iUnion fun k => measurableSet_successEvent k
  apply (ae_iff_measure_eq (μ := BernoulliSequenceMeasure x)
    hm.nullMeasurableSet).2
  simpa using hmeasure

def firstAtEvent (k : Nat) : Set (Nat → Bool) :=
  successEvent k ∩ ⋂ i : Fin k, {b | b i.val = false}

def noSuccessEvent : Set (Nat → Bool) := {b | ¬ hasSuccess b}

theorem measurableSet_firstAtEvent (k : Nat) : MeasurableSet (firstAtEvent k) := by
  apply (measurableSet_successEvent k).inter
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_singleton false).preimage (measurable_pi_apply i.val)

theorem measurableSet_noSuccessEvent : MeasurableSet noSuccessEvent := by
  rw [show noSuccessEvent = ⋂ k, {b : Nat → Bool | b k = false} by
    ext b
    simp [noSuccessEvent, hasSuccess]]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_singleton false).preimage (measurable_pi_apply k)

theorem firstSuccess_fiber (k : Nat) :
    {b : Nat → Bool | firstSuccess b = k} =
      firstAtEvent k ∪ (if k = 0 then noSuccessEvent else ∅) := by
  ext b
  constructor
  · intro hb
    by_cases hs : hasSuccess b
    · left
      constructor
      · rw [← hb]
        exact firstSuccess_spec b hs
      · simp only [Set.mem_iInter]
        intro i
        exact firstSuccess_before b hs (by rw [hb]; exact i.isLt)
    · right
      have hs' : ¬ ∃ k, b k = true := hs
      have hk : k = 0 := by
        simp [firstSuccess, hs'] at hb
        exact hb.symm
      simp [hk, noSuccessEvent, hs]
  · intro hb
    rcases hb with hb | hb
    · simp only [firstAtEvent, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, successEvent] at hb
      exact firstSuccess_eq_of_first b k hb.1 (by
        intro i hi
        have := hb.2 (⟨i, hi⟩ : Fin k)
        simpa using this)
    · by_cases hk : k = 0
      · subst k
        have hno : b ∈ noSuccessEvent := by simpa using hb
        have hs' : ¬ ∃ k, b k = true := hno
        change firstSuccess b = 0
        unfold firstSuccess
        rw [dif_neg hs']
      · simp [hk] at hb

theorem measurableSet_firstSuccess_fiber (k : Nat) :
    MeasurableSet {b : Nat → Bool | firstSuccess b = k} := by
  rw [firstSuccess_fiber]
  apply (measurableSet_firstAtEvent k).union
  split_ifs
  · exact measurableSet_noSuccessEvent
  · exact MeasurableSet.empty

theorem measurable_firstSuccess : Measurable firstSuccess := by
  intro s hs
  rw [show firstSuccess ⁻¹' s = ⋃ k : {k // k ∈ s},
      {b : Nat → Bool | firstSuccess b = k.val} by
    ext b
    simp]
  exact MeasurableSet.iUnion fun k => measurableSet_firstSuccess_fiber k.val

def failureEvent (k : Nat) : Set (Nat → Bool) := {b | b k = false}

theorem measurableSet_failureEvent (k : Nat) : MeasurableSet (failureEvent k) := by
  exact measurableSet_singleton false |>.preimage (measurable_pi_apply k)

theorem bernoulliSequenceMeasure_failureEvent (x : I) (k : Nat) :
    BernoulliSequenceMeasure x (failureEvent k) =
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) := by
  rw [show failureEvent k = (fun b : Nat → Bool => b k) ⁻¹' {false} by rfl]
  rw [← Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton false)]
  rw [Measure.infinitePi_map_eval]
  simp [BernoulliBitMeasure]

theorem firstAtEvent_eq_biInter (k : Nat) :
    firstAtEvent k = ⋂ i ∈ Finset.range (k + 1),
      if i = k then successEvent i else failureEvent i := by
  ext b
  simp only [firstAtEvent, Set.mem_inter_iff, successEvent, failureEvent,
    Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hb i hi
    split_ifs with hik
    · subst i
      exact hb.1
    · exact hb.2 ⟨i, by simp at hi; omega⟩
  · intro hb
    constructor
    · have h := hb k (by simp)
      simpa using h
    · intro i
      have h := hb i.val (by simp)
      simpa [show i.val ≠ k by omega] using h

theorem bernoulliSequenceMeasure_firstAtEvent (x : I) (k : Nat) :
    BernoulliSequenceMeasure x (firstAtEvent k) =
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ k *
        (unitInterval.toNNReal x : ENNReal) := by
  rw [firstAtEvent_eq_biInter]
  have hi : iIndepFun (fun i (b : Nat → Bool) => b i)
      (BernoulliSequenceMeasure x) :=
    iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)
  rw [hi.meas_biInter (fun i _ => by
    split_ifs
    · exact MeasurableSpace.measurableSet_comap.mpr
        ⟨{true}, measurableSet_singleton true, rfl⟩
    · exact MeasurableSpace.measurableSet_comap.mpr
        ⟨{false}, measurableSet_singleton false, rfl⟩)]
  rw [Finset.prod_range_succ]
  simp only [if_pos]
  congr 1
  · calc
      ∏ i ∈ Finset.range k,
          BernoulliSequenceMeasure x
            (if i = k then successEvent i else failureEvent i) =
          ∏ _i ∈ Finset.range k,
            (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hi))]
        exact bernoulliSequenceMeasure_failureEvent x i
      _ = (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ k := by
        simp
  · exact bernoulliSequenceMeasure_successEvent x k

theorem bernoulliSequenceMeasure_noSuccessEvent {x : I} (hx : x ≠ 0) :
    BernoulliSequenceMeasure x noSuccessEvent = 0 := by
  have h := (ae_iff.mp (ae_hasSuccess hx))
  simpa [noSuccessEvent] using h

theorem firstAtEvent_disjoint_noSuccessEvent (k : Nat) :
    Disjoint (firstAtEvent k) noSuccessEvent := by
  rw [Set.disjoint_left]
  intro b hb hno
  exact hno ⟨k, hb.1⟩

theorem bernoulliSequenceMeasure_firstSuccess_fiber {x : I} (hx : x ≠ 0)
    (k : Nat) :
    BernoulliSequenceMeasure x {b : Nat → Bool | firstSuccess b = k} =
      (unitInterval.toNNReal (unitInterval.symm x) : ENNReal) ^ k *
        (unitInterval.toNNReal x : ENNReal) := by
  rw [firstSuccess_fiber]
  by_cases hk : k = 0
  · rw [if_pos hk]
    rw [measure_union (firstAtEvent_disjoint_noSuccessEvent k)
      measurableSet_noSuccessEvent]
    rw [bernoulliSequenceMeasure_noSuccessEvent hx, add_zero]
    exact bernoulliSequenceMeasure_firstAtEvent x k
  · rw [if_neg hk, union_empty]
    exact bernoulliSequenceMeasure_firstAtEvent x k

theorem firstSuccess_has_geometric_law {x : I} (hx : x ≠ 0) :
    (BernoulliSequenceMeasure x).map firstSuccess = geometricMeasure x := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply measurable_firstSuccess (measurableSet_singleton k)]
  rw [show firstSuccess ⁻¹' ({k} : Set Nat) =
      {b : Nat → Bool | firstSuccess b = k} by ext; simp]
  rw [bernoulliSequenceMeasure_firstSuccess_fiber hx k]
  rw [geometricMeasure_singleton hx]
  rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by simp)) (by simp))]
  rw [← ENNReal.ofReal_toReal (by simp :
      ENNReal.ofReal ((1 - (x : Real)) ^ k * (x : Real)) ≠ ⊤)]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  simp only [ENNReal.coe_toReal]
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg x k)]
  rfl

/-! ## One common space for both infinite sides

The actual finite marker lists are the literal initial segments of the two
infinite streams.  Hence the remaining coordinates are genuine independent
dummy tails, rather than separately sampled marginals pasted together. -/

abbrev InfiniteDummyPairMeasure (x : I) :
    Measure ((Nat → Bool) × (Nat → Bool)) :=
  (BernoulliSequenceMeasure x).prod (BernoulliSequenceMeasure x)

instance infiniteDummyPairMeasure_isProbability (x : I) :
    IsProbabilityMeasure (InfiniteDummyPairMeasure x) := inferInstance

def streamPrefix (m : Nat) (b : Nat → Bool) : List Bool :=
  List.ofFn fun i : Fin m => b i.val

@[simp] theorem streamPrefix_length (m : Nat) (b : Nat → Bool) :
    (streamPrefix m b).length = m := by simp [streamPrefix]

theorem truncatedWait_le_of_getElem_true (xs : List Bool) (r : Nat)
    (hr : r < xs.length) (htrue : xs[r] = true) :
    truncatedWait xs ≤ r + 1 := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons a xs ih =>
      cases r with
      | zero =>
          simp only [List.getElem_cons_zero] at htrue
          subst a
          simp
      | succ r =>
          have hr' : r < xs.length := by simpa using hr
          have ht' : xs[r] = true := by simpa using htrue
          cases a
          · simp only [truncatedWait]
            have := ih r hr' ht'
            omega
          · simp

/-- A finite genuine prefix never waits longer than the first success of the
same infinite stream.  The `hasSuccess` hypothesis is almost sure for
`x ≠ 0`, proved above. -/
theorem truncatedWait_streamPrefix_le_firstSuccess_add_one
    (m : Nat) (b : Nat → Bool) (hs : hasSuccess b) :
    truncatedWait (streamPrefix m b) ≤ firstSuccess b + 1 := by
  by_cases hlt : firstSuccess b < m
  · refine truncatedWait_le_of_getElem_true _ (firstSuccess b)
      (hr := by simpa using hlt) ?_
    simp [streamPrefix, firstSuccess_spec b hs]
  · have hlen := truncatedWait_le_length_succ (streamPrefix m b)
    simp only [streamPrefix_length] at hlen
    omega

def infiniteDummyWaitPair (z : (Nat → Bool) × (Nat → Bool)) : Nat × Nat :=
  (firstSuccess z.1, firstSuccess z.2)

theorem measurable_infiniteDummyWaitPair : Measurable infiniteDummyWaitPair := by
  exact (measurable_firstSuccess.comp measurable_fst).prod
    (measurable_firstSuccess.comp measurable_snd)

/-- The two first-success indices are jointly, not merely marginally,
independent Mathlib geometric variables. -/
theorem infiniteDummyWaitPair_has_geometric_pair_law {x : I} (hx : x ≠ 0) :
    (InfiniteDummyPairMeasure x).map infiniteDummyWaitPair =
      GeometricPairMeasure x := by
  rw [show infiniteDummyWaitPair = Prod.map firstSuccess firstSuccess by
    funext z
    rfl]
  rw [← Measure.map_prod_map _ _ measurable_firstSuccess measurable_firstSuccess]
  rw [firstSuccess_has_geometric_law hx]

theorem measurableSet_hasSuccess : MeasurableSet {b : Nat → Bool | hasSuccess b} := by
  rw [show {b | hasSuccess b} = ⋃ k, successEvent k by
    ext b
    simp [hasSuccess, successEvent]]
  exact MeasurableSet.iUnion fun k => measurableSet_successEvent k

theorem ae_infiniteDummyPair_hasSuccess {x : I} (hx : x ≠ 0) :
    ∀ᵐ z ∂(InfiniteDummyPairMeasure x), hasSuccess z.1 ∧ hasSuccess z.2 := by
  refine (Measure.ae_prod_iff_ae_ae (p := fun z =>
    hasSuccess z.1 ∧ hasSuccess z.2)
    ((measurableSet_hasSuccess.preimage measurable_fst).inter
      (measurableSet_hasSuccess.preimage measurable_snd))).2 ?_
  filter_upwards [ae_hasSuccess hx] with left hleft
  filter_upwards [ae_hasSuccess hx] with right hright
  exact ⟨hleft, hright⟩

/-- Simultaneous pointwise domination of both actual finite prefixes on the
same sample that generates the independent geometric pair. -/
theorem ae_truncatedWait_prefix_pair_le_geometric {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) :
    ∀ᵐ z ∂(InfiniteDummyPairMeasure x),
      truncatedWait (streamPrefix leftLen z.1) ≤ firstSuccess z.1 + 1 ∧
      truncatedWait (streamPrefix rightLen z.2) ≤ firstSuccess z.2 + 1 := by
  filter_upwards [ae_infiniteDummyPair_hasSuccess hx] with z hz
  exact ⟨truncatedWait_streamPrefix_le_firstSuccess_add_one leftLen z.1 hz.1,
    truncatedWait_streamPrefix_le_firstSuccess_add_one rightLen z.2 hz.2⟩

theorem iIndepFun_sequenceCoordinates (x : I) :
    iIndepFun (fun i (b : Nat → Bool) => b i) (BernoulliSequenceMeasure x) :=
  iIndepFun_infinitePi (X := fun _ b => b) (fun _ => measurable_id)

def streamPrefixVector (m : Nat) (b : Nat → Bool) : Fin m → Bool :=
  fun i => b i.val

theorem measurable_streamPrefixVector (m : Nat) :
    Measurable (streamPrefixVector m) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply i.val

/-- Exact joint law of every coordinate in one finite shared prefix. -/
theorem map_streamPrefixVector (x : I) (m : Nat) :
    (BernoulliSequenceMeasure x).map (streamPrefixVector m) =
      Measure.pi (fun _ : Fin m => BernoulliBitMeasure x) := by
  have hi : iIndepFun
      (fun i : Fin m => fun b : Nat → Bool => b i.val)
      (BernoulliSequenceMeasure x) :=
    (iIndepFun_sequenceCoordinates x).precomp (g := fun i : Fin m => i.val)
      Fin.val_injective
  change (BernoulliSequenceMeasure x).map (fun b i => b i.val) =
    Measure.pi (fun _ : Fin m => BernoulliBitMeasure x)
  rw [hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply i.val).aemeasurable)]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval (fun _ : Nat => BernoulliBitMeasure x) i.val

def pairedPrefixVector (leftLen rightLen : Nat)
    (z : (Nat → Bool) × (Nat → Bool)) :
    (Fin leftLen → Bool) × (Fin rightLen → Bool) :=
  (streamPrefixVector leftLen z.1, streamPrefixVector rightLen z.2)

theorem measurable_pairedPrefixVector (leftLen rightLen : Nat) :
    Measurable (pairedPrefixVector leftLen rightLen) := by
  exact ((measurable_streamPrefixVector leftLen).comp measurable_fst).prod
    ((measurable_streamPrefixVector rightLen).comp measurable_snd)

/-- The two genuine finite prefixes have one exact product law.  This is the
pair presentation of the disjoint-sum Bernoulli law proved for
`actualMarkerBits`; no marginal-to-joint inference occurs. -/
theorem map_pairedPrefixVector (x : I) (leftLen rightLen : Nat) :
    (InfiniteDummyPairMeasure x).map
        (pairedPrefixVector leftLen rightLen) =
      (Measure.pi (fun _ : Fin leftLen => BernoulliBitMeasure x)).prod
        (Measure.pi (fun _ : Fin rightLen => BernoulliBitMeasure x)) := by
  rw [show pairedPrefixVector leftLen rightLen =
      Prod.map (streamPrefixVector leftLen) (streamPrefixVector rightLen) by
    funext z
    rfl]
  rw [← Measure.map_prod_map _ _ (measurable_streamPrefixVector leftLen)
    (measurable_streamPrefixVector rightLen)]
  rw [map_streamPrefixVector, map_streamPrefixVector]

def actualMarkerPair {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) :
    (Fin j.val → Bool) × (Fin (q - (j.val + 1)) → Bool) :=
  ((fun i => actualMarkerBits E base j hbaseTarget x (Sum.inl i) ω),
    fun i => actualMarkerBits E base j hbaseTarget x (Sum.inr i) ω)

/-- The canonical shared prefixes and the genuine stable-marriage marker
bits have exactly the same *joint* law, after the canonical sum/function
equivalence. -/
theorem map_actualMarkerPair_eq_pairedPrefixVector {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) :
    (TargetOtherPriorityMeasure target).map
        (actualMarkerPair E base j hbaseTarget x) =
      (InfiniteDummyPairMeasure x).map
        (pairedPrefixVector j.val (q - (j.val + 1))) := by
  have hvec : Measurable (fun ω s =>
      actualMarkerBits E base j hbaseTarget x s ω) :=
    measurable_pi_lambda _ fun s =>
      measurable_actualMarkerBit E base j hbaseTarget x s
  have hpair : actualMarkerPair E base j hbaseTarget x =
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : MarkerSideIndex j => Bool)) ∘
        (fun ω s => actualMarkerBits E base j hbaseTarget x s ω) := by
    funext ω
    rfl
  rw [hpair, ← Measure.map_map
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : MarkerSideIndex j => Bool)).measurable hvec]
  rw [map_actualMarkerBits E base j hbaseTarget x]
  rw [(measurePreserving_sumPiEquivProdPi
    (fun _ : MarkerSideIndex j => BernoulliBitMeasure x)).map_eq]
  rw [map_pairedPrefixVector]

def dummyTail (m : Nat) (b : Nat → Bool) : Nat → Bool := fun k => b (m + k)

@[simp] theorem sharedPrefix_apply (m : Nat) (b : Nat → Bool) (i : Fin m) :
    streamPrefixVector m b i = b i.val := rfl

@[simp] theorem sharedDummyTail_apply (m : Nat) (b : Nat → Bool) (k : Nat) :
    dummyTail m b k = b (m + k) := rfl

/-- The finite actual window is dominated on the same sample by the
two-geometric window used by `GeometricIntegral`. -/
theorem ae_markerWindowWidth_prefix_le_geometricWindow {x : I} (hx : x ≠ 0)
    (leftLen rightLen : Nat) :
    ∀ᵐ z ∂(InfiniteDummyPairMeasure x),
      markerWindowWidth (streamPrefix leftLen z.1) (streamPrefix rightLen z.2) ≤
        geometricWindow (infiniteDummyWaitPair z) := by
  filter_upwards [ae_truncatedWait_prefix_pair_le_geometric hx leftLen rightLen] with z hz
  simp only [markerWindowWidth, geometricWindow, infiniteDummyWaitPair]
  omega

end

end StableMatchingsE2E
