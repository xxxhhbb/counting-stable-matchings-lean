import StableMatchingsE2E.MarkerWindowBridge
import StableMatchingsE2E.RandomPriorities
import StableMatchingsProbability.Core
import Mathlib.Probability.Distributions.Geometric

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal
open StableMatchings355 StableMatchingsEntropy

noncomputable section

attribute [local instance] Classical.propDecidable

/-!  The indices on the two sides of the distinguished partner are bundled
into one finite type.  This is the exact index set whose coordinates must be
shown distinct before any appeal to independence. -/

abbrev MarkerSideIndex {q : Nat} (j : Fin q) :=
  Fin j.val ⊕ Fin (q - (j.val + 1))

def markerRank {q : Nat} (j : Fin q) : MarkerSideIndex j → Fin q
  | Sum.inl i => leftMarkerIndex j i
  | Sum.inr i => rightMarkerIndex j i

theorem markerRank_ne_center {q : Nat} (j : Fin q)
    (s : MarkerSideIndex j) : markerRank j s ≠ j := by
  cases s with
  | inl i =>
      intro h
      have hv := congrArg Fin.val h
      simp [markerRank, leftMarkerIndex] at hv
      omega
  | inr i =>
      intro h
      have hv := congrArg Fin.val h
      simp [markerRank, rightMarkerIndex] at hv
      omega

theorem markerRank_injective {q : Nat} (j : Fin q) :
    Function.Injective (markerRank j) := by
  intro s t h
  cases s with
  | inl i =>
      cases t with
      | inl i' =>
          apply congrArg Sum.inl
          apply Fin.eq_of_val_eq
          have hv := congrArg Fin.val h
          simp [markerRank, leftMarkerIndex] at hv
          omega
      | inr i' =>
          have hv := congrArg Fin.val h
          simp [markerRank, leftMarkerIndex, rightMarkerIndex] at hv
          omega
  | inr i =>
      cases t with
      | inl i' =>
          have hv := congrArg Fin.val h
          simp [markerRank, leftMarkerIndex, rightMarkerIndex] at hv
          omega
      | inr i' =>
          apply congrArg Sum.inr
          apply Fin.eq_of_val_eq
          have hv := congrArg Fin.val h
          simp [markerRank, rightMarkerIndex] at hv
          omega

/-- The actual man owning a marker coordinate, packaged as a non-target man.
The non-target proof is not a probabilistic assumption: it follows from the
exact stable-partner enumeration and the fact that the coordinate is not the
central rank. -/
def markerOwnerOther {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (s : MarkerSideIndex j) : OtherMen target :=
  ⟨stablePartnerOwner E base (markerRank j s),
    stablePartnerOwner_ne_target E base hbaseTarget
      (markerRank_ne_center j s)⟩

theorem markerOwnerOther_injective {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j) :
    Function.Injective (markerOwnerOther E base j hbaseTarget) := by
  intro s t h
  apply markerRank_injective j
  apply stablePartnerOwner_injective E base
  exact congrArg Subtype.val h

/-- All genuine left/right marker bits at a fixed target threshold, directly
on the product space of the other men. -/
def actualMarkerBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) : MarkerSideIndex j → (OtherMen target → I) → Bool :=
  fun s ω => revealIndicator x (ω (markerOwnerOther E base j hbaseTarget s))

theorem iIndepFun_actualMarkerBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) :
    iIndepFun (actualMarkerBits E base j hbaseTarget x)
      (TargetOtherPriorityMeasure target) := by
  exact (iIndepFun_targetOtherIndicators target x).precomp
    (g := markerOwnerOther E base j hbaseTarget)
    (markerOwnerOther_injective E base j hbaseTarget)

theorem measurable_actualMarkerBit {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (s : MarkerSideIndex j) :
    Measurable (actualMarkerBits E base j hbaseTarget x s) := by
  exact (measurable_revealIndicator x).comp
    (measurable_pi_apply (markerOwnerOther E base j hbaseTarget s))

/-- Exact joint law of every genuine left and right marker bit.  In
particular, left/right independence is not inferred merely from marginal
Bernoulli laws: it is a single product-law identity indexed by the disjoint
sum of both sides. -/
theorem map_actualMarkerBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) :
    (TargetOtherPriorityMeasure target).map
        (fun ω s => actualMarkerBits E base j hbaseTarget x s ω) =
      Measure.pi (fun _ : MarkerSideIndex j => Ber(true, false, x)) := by
  rw [(iIndepFun_actualMarkerBits E base j hbaseTarget x).map_fun_eq_pi_map
    (fun s => (measurable_actualMarkerBit E base j hbaseTarget x s).aemeasurable)]
  congr 1
  funext s
  exact map_targetOtherIndicator target x
    (markerOwnerOther E base j hbaseTarget s)

def actualLeftBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) : List Bool :=
  List.ofFn fun i : Fin j.val =>
    actualMarkerBits E base j hbaseTarget x (Sum.inl i) ω

def actualRightBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) : List Bool :=
  List.ofFn fun i : Fin (q - (j.val + 1)) =>
    actualMarkerBits E base j hbaseTarget x (Sum.inr i) ω

theorem ownerMarkerBit_split_eq_indicator {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) (s : MarkerSideIndex j) :
    ownerMarkerBit E base
        (UnitRevealedBefore (assemblePriority target (x, ω)) target)
        (markerRank j s) =
      actualMarkerBits E base j hbaseTarget x s ω := by
  classical
  unfold ownerMarkerBit actualMarkerBits revealIndicator
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact unitRevealedBefore_assemble_other_iff target
      (stablePartnerOwner E base (markerRank j s)) (x, ω)
      (stablePartnerOwner_ne_target E base hbaseTarget
        (markerRank_ne_center j s))

theorem leftMarkerBits_split_eq_actual {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) :
    leftMarkerBits E base
        (UnitRevealedBefore (assemblePriority target (x, ω)) target) j =
      actualLeftBits E base j hbaseTarget x ω := by
  classical
  unfold leftMarkerBits actualLeftBits
  congr 1
  funext i
  exact ownerMarkerBit_split_eq_indicator E base j hbaseTarget x ω (Sum.inl i)

theorem rightMarkerBits_split_eq_actual {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I) :
    rightMarkerBits E base
        (UnitRevealedBefore (assemblePriority target (x, ω)) target) j =
      actualRightBits E base j hbaseTarget x ω := by
  classical
  unfold rightMarkerBits actualRightBits
  congr 1
  funext i
  exact ownerMarkerBit_split_eq_indicator E base j hbaseTarget x ω (Sum.inr i)

/-- Pointwise stable-matching support bound expressed on exactly the random
bit vector whose joint product law was established above. -/
theorem exact_support_le_actual_marker_window {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbase : Stable P base)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I)
    (W : NearestRevealedWindow E base
      (UnitRevealedBefore (assemblePriority target (x, ω)) target) j)
    (S : ExactConditionalIndexSupport P E base
      (UnitRevealedBefore (assemblePriority target (x, ω)) target)) :
    S.indices.length ≤ markerWindowWidth
      (actualLeftBits E base j hbaseTarget x ω)
      (actualRightBits E base j hbaseTarget x ω) := by
  classical
  rw [← leftMarkerBits_split_eq_actual E base j hbaseTarget x ω,
    ← rightMarkerBits_split_eq_actual E base j hbaseTarget x ω]
  exact exact_conditional_support_length_le_markerWindowWidth
    P E base _ hbase hbaseTarget W S

/-- Fully pointwise finite dummy-extension coupling.  No independence claim
is needed for this order statement; independence enters only when a product
measure is put on the dummy bits. -/
theorem exact_support_le_dummy_extended_window {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbase : Stable P base)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) (ω : OtherMen target → I)
    (leftDummy rightDummy : List Bool)
    (W : NearestRevealedWindow E base
      (UnitRevealedBefore (assemblePriority target (x, ω)) target) j)
    (S : ExactConditionalIndexSupport P E base
      (UnitRevealedBefore (assemblePriority target (x, ω)) target)) :
    S.indices.length ≤ markerWindowWidth
      (actualLeftBits E base j hbaseTarget x ω ++ leftDummy)
      (actualRightBits E base j hbaseTarget x ω ++ rightDummy) := by
  classical
  apply conditional_support_le_extended_marker_window
  exact exact_support_le_actual_marker_window P E base j hbase hbaseTarget x ω W S

/-! ## The independent geometric comparison space

Mathlib's `geometricMeasure x` is zero based.  Consequently `G₀ + 1` is
the positive waiting time used by `truncatedWait`, and the two-sided window
is `G₀,left + G₀,right + 1`.  The endpoint `x = 0` is deliberately kept:
Mathlib defines it as `dirac 0`; statements using the usual geometric mass
therefore carry the necessary `x ≠ 0` hypothesis explicitly. -/

abbrev GeometricPairMeasure (x : I) : Measure (Nat × Nat) :=
  (geometricMeasure x).prod (geometricMeasure x)

instance geometricPairMeasure_isProbability (x : I) :
    IsProbabilityMeasure (GeometricPairMeasure x) := inferInstance

def geometricLeft (z : Nat × Nat) : Nat := z.1
def geometricRight (z : Nat × Nat) : Nat := z.2
def geometricWindow (z : Nat × Nat) : Nat := z.1 + z.2 + 1

theorem geometricWindow_pos (z : Nat × Nat) : 1 ≤ geometricWindow z := by
  simp [geometricWindow]

/-- Each positive split of `k` has exactly the claimed product mass.  This
is the atom-level identity used by the finite disjoint-union calculation of
the law of the two-geometric window. -/
theorem geometric_pair_atom_real {x : I} (hx : x ≠ 0)
    {k L R : Nat} (h : (L, R) ∈ geometricSplits k) :
    (geometricMeasure x).real {L - 1} *
        (geometricMeasure x).real {R - 1} =
      ((x : Real) ^ 2 * (1 - (x : Real)) ^ (k - 1)) := by
  rw [geometricMeasure_real_singleton hx, geometricMeasure_real_singleton hx]
  have hs := mem_geometricSplits_iff.mp h
  have he := geometric_split_failure_exponent h
  calc
    (1 - (x : Real)) ^ (L - 1) * (x : Real) *
          ((1 - (x : Real)) ^ (R - 1) * (x : Real)) =
        (x : Real) ^ 2 *
          ((1 - (x : Real)) ^ (L - 1) *
            (1 - (x : Real)) ^ (R - 1)) := by ring
    _ = (x : Real) ^ 2 * (1 - (x : Real)) ^ (k - 1) := by
      rw [← pow_add, he]

/-- The exact algebraic factor in the law
`P(G_left + G_right + 1 = k) = k*x^2*(1-x)^(k-1)`.  The remaining measure
step is a finite disjoint union of the atoms indexed by `geometricSplits k`;
this lemma ensures no analytic or asymptotic argument is hidden in the
convolution coefficient. -/
theorem geometric_window_mass_factor {x : I} (hx : x ≠ 0) (k : Nat) :
    ∑ p ∈ (geometricSplits k).toFinset,
        ((geometricMeasure x).real {p.1 - 1} *
          (geometricMeasure x).real {p.2 - 1}) =
      (k : Real) * ((x : Real) ^ 2 * (1 - (x : Real)) ^ (k - 1)) := by
  classical
  have hconst : ∀ p ∈ (geometricSplits k).toFinset,
      (geometricMeasure x).real {p.1 - 1} *
          (geometricMeasure x).real {p.2 - 1} =
        ((x : Real) ^ 2 * (1 - (x : Real)) ^ (k - 1)) := by
    intro p hp
    exact geometric_pair_atom_real hx (by simpa using hp)
  calc
    ∑ p ∈ (geometricSplits k).toFinset,
        ((geometricMeasure x).real {p.1 - 1} *
          (geometricMeasure x).real {p.2 - 1}) =
        ∑ _p ∈ (geometricSplits k).toFinset,
          ((x : Real) ^ 2 * (1 - (x : Real)) ^ (k - 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hconst p hp
    _ = (k : Real) * ((x : Real) ^ 2 *
          (1 - (x : Real)) ^ (k - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [List.toFinset_card_of_nodup (geometricSplits_nodup k),
        geometricSplits_length]

def geometricAtom (p : Nat × Nat) : Nat × Nat :=
  (p.1 - 1, p.2 - 1)

theorem geometricWindow_fiber (k : Nat) :
    {z : Nat × Nat | geometricWindow z = k} =
      ⋃ p ∈ (geometricSplits k).toFinset, ({geometricAtom p} : Set (Nat × Nat)) := by
  ext z
  constructor
  · intro hz
    have hk : 1 ≤ k := by
      simp only [Set.mem_setOf_eq, geometricWindow] at hz
      omega
    let p : Nat × Nat := (z.1 + 1, z.2 + 1)
    have hp : p ∈ geometricSplits k := by
      apply mem_geometricSplits_iff.mpr
      simp
      simpa [geometricWindow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hz
    simp only [Set.mem_iUnion]
    refine ⟨p, ?_⟩
    refine ⟨by simpa using hp, ?_⟩
    simp [geometricAtom, p]
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    have hp' : p ∈ geometricSplits k := by simpa using hp
    have hs := mem_geometricSplits_iff.mp hp'
    have hz' : z = geometricAtom p := by simpa using hzp
    subst z
    simp only [Set.mem_setOf_eq, geometricWindow, geometricAtom]
    omega

theorem geometricPairMeasure_real_singleton (x : I) (a b : Nat) :
    (GeometricPairMeasure x).real {(a, b)} =
      (geometricMeasure x).real {a} * (geometricMeasure x).real {b} := by
  rw [show ({(a, b)} : Set (Nat × Nat)) = ({a} : Set Nat) ×ˢ ({b} : Set Nat) by
    ext z
    simp [Prod.ext_iff]]
  exact measureReal_prod_prod _ _

/-- Exact law of the positive two-geometric window, as a statement about
the product of two independent Mathlib geometric measures. -/
theorem geometricWindow_real_fiber {x : I} (hx : x ≠ 0) (k : Nat) :
    (GeometricPairMeasure x).real {z : Nat × Nat | geometricWindow z = k} =
      (k : Real) * ((x : Real) ^ 2 *
        (1 - (x : Real)) ^ (k - 1)) := by
  rw [geometricWindow_fiber]
  rw [measureReal_biUnion_finset]
  · simp_rw [geometricAtom, geometricPairMeasure_real_singleton]
    exact geometric_window_mass_factor hx k
  · intro p hp r hr hpr
    simp only [Function.onFun, Set.disjoint_singleton]
    intro heq
    apply hpr
    have hp' : p ∈ geometricSplits k := by simpa using hp
    have hr' : r ∈ geometricSplits k := by simpa using hr
    have hpp := mem_geometricSplits_iff.mp hp'
    have hrr := mem_geometricSplits_iff.mp hr'
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    simp only [geometricAtom] at h1 h2
    apply Prod.ext <;> omega
  · intro p hp
    exact measurableSet_singleton _

/-- Endpoint audit.  Mathlib totalizes the zero-parameter geometric law as
`dirac 0`; hence the comparison window is deterministically one at `x = 0`.
The usual formula with a factor `x²` is intentionally *not* asserted there
(it would give zero mass everywhere and is not a probability law). -/
theorem geometricPairMeasure_zero :
    GeometricPairMeasure (0 : I) = Measure.dirac (0, 0) := by
  simp [GeometricPairMeasure, geometricMeasure, Measure.dirac_prod_dirac]

theorem geometricWindow_zero_fiber (k : Nat) :
    (GeometricPairMeasure (0 : I)).real
        {z : Nat × Nat | geometricWindow z = k} =
      if k = 1 then 1 else 0 := by
  rw [geometricPairMeasure_zero]
  by_cases hk : k = 1
  · subst k
    simp [measureReal_def, geometricWindow]
  · have hk' : (0 : Nat) + 0 + 1 ≠ k := by omega
    simp [measureReal_def, geometricWindow, hk, hk']

end

end StableMatchingsE2E
