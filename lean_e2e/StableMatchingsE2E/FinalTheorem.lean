import StableMatchingsE2E.EntropyRandomOrder
import StableMatchingsE2E.InfiniteDummyCoupling
import StableMatchingsE2E.ConstantCertificate
import StableMatchingsE2E.FinalTargets
import Mathlib.Data.List.Indexes

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy

noncomputable section

private theorem exp_nat_mul_log_eq_pow_final {q : ℝ} (hq : 0 < q)
    (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log q) = q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Real.exp_add, ih, pow_succ]
      simp [Real.exp_log hq]

private theorem log_lt_to_nat_crossmul_17_5_final {n a : ℕ}
    (ha : 0 < a)
    (hlog : Real.log (a : ℝ) <
      (n : ℝ) * Real.log ((17 : ℝ) / 5)) :
    5 ^ n * a < 17 ^ n := by
  have hq : (0 : ℝ) < (17 : ℝ) / 5 := by norm_num
  have hexp := (Real.exp_lt_exp).mpr hlog
  rw [Real.exp_log (by exact_mod_cast ha),
    exp_nat_mul_log_eq_pow_final hq n] at hexp
  have hfive : 0 < (5 : ℝ) ^ n := pow_pos (by norm_num) n
  have hmul := mul_lt_mul_of_pos_left hexp hfive
  rw [div_pow] at hmul
  field_simp at hmul
  exact_mod_cast hmul

private theorem zero_lt_nat_target_17_final {n : ℕ} : 0 < 17 ^ n := by
  exact pow_pos (by norm_num) n

/-! # End-to-end assembly

This file contains only glue.  In particular, it makes explicit the
target/other-priority change of variables and does not condition on the
measure-zero event that a sampled priority is equal to a fixed threshold.
-/

/-- The target/other split really is the full independent-priority law. -/
theorem map_assemblePriority_splitTargetPriorityMeasure {n : Nat}
    (target : Fin n) :
    (SplitTargetPriorityMeasure target).map (assemblePriority target) =
      FullPriorityMeasure n := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_assemblePriority target) (.univ_pi hs)]
  have hpre :
      assemblePriority target ⁻¹' (Set.univ.pi s) =
        s target ×ˢ (Set.univ.pi fun i : OtherMen target => s i.1) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod]
    constructor
    · intro hz
      constructor
      · simpa only [assemblePriority_target] using hz target
      · intro i
        simpa only [assemblePriority_other target i.1 z i.2] using hz i.1
    · rintro ⟨ht, ho⟩ p
      by_cases hp : p = target
      · subst p
        simpa only [assemblePriority_target] using ht
      · simpa only [assemblePriority_other target p z hp] using
          ho (⟨p, hp⟩ : OtherMen target)
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  calc
    (volume : Measure I) (s target) *
          ∏ i : OtherMen target, (volume : Measure I) (s i.1) =
        (volume : Measure I) (s target) *
          ∏ p ∈ Finset.univ.erase target, (volume : Measure I) (s p) := by
      rw [Finset.prod_subtype (p := fun p : Fin n => p ≠ target)
        (s := Finset.univ.erase target) (by intro p; simp)
        (fun p : Fin n => (volume : Measure I) (s p))]
    _ = ∏ p : Fin n, (volume : Measure I) (s p) :=
      Finset.mul_prod_erase Finset.univ
        (fun p : Fin n => (volume : Measure I) (s p))
        (Finset.mem_univ target)

/-! ## A selector with non-adaptive partner enumerations

The enumeration for a target is chosen once, before the reveal set and the
base stable matching are supplied.  Only the nearest-window witness depends
on the reveal prefix.  This is the key reason the later Bernoulli law applies
to one fixed injective family of owner coordinates.
-/

structure StaticWindowData {n : Nat} (P : ProfileCode n) where
  q : Fin n → Nat
  enumeration : (m : Fin n) →
    ExactStablePartnerEnumeration (q := q m) P.toCore m
  center : (base : StableBase P) → (m : Fin n) → Fin (q m)
  center_spec : ∀ (base : StableBase P) (m : Fin n),
    base.1.toCore.manPartner m = (enumeration m).ranked.partner (center base m)
  window : (seen : List (Fin n)) → (base : StableBase P) → (m : Fin n) →
    NearestRevealedWindow (enumeration m) base.1.toCore
      (listRevealed seen) (center base m)
  support : (seen : List (Fin n)) → (base : StableBase P) → (m : Fin n) →
    ExactConditionalIndexSupport P.toCore (enumeration m) base.1.toCore
      (listRevealed seen)

theorem exists_staticWindowData {n : Nat} (P : ProfileCode n) :
    Nonempty (StaticWindowData P) := by
  classical
  choose q hq using fun m : Fin n ↦
    exists_exactStablePartnerEnumeration P.toCore m
  let E : (m : Fin n) →
      ExactStablePartnerEnumeration (q := q m) P.toCore m :=
    fun m ↦ Classical.choice (hq m)
  choose center hcenter using fun (base : StableBase P) (m : Fin n) ↦
    (E m).complete base.1.toCore
      ((stableCode_iff_core P base.1).1 base.2)
  let W := fun (seen : List (Fin n)) (base : StableBase P) (m : Fin n) ↦
    Classical.choice (exists_nearestRevealedWindow (E m) base.1.toCore
      (listRevealed seen) (center base m))
  let S := fun (seen : List (Fin n)) (base : StableBase P) (m : Fin n) ↦
    Classical.choice (exists_exactConditionalIndexSupport P.toCore
      (E m) base.1.toCore (listRevealed seen))
  exact ⟨{
    q := q
    enumeration := E
    center := center
    center_spec := hcenter
    window := W
    support := S }⟩

def StaticWindowData.selector {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) : PrefixWindowSelector P :=
  fun seen m base ↦
    { q := D.q m
      enumeration := D.enumeration m
      center := D.center base m
      base_eq := D.center_spec base m
      window := D.window seen base m
      support := D.support seen base m
      support_card_le := by
        exact conditionalPartnerSupport_card_le_window P m
          (D.enumeration m) base.1 (listRevealed seen) base.2
          (D.center_spec base m) (D.window seen base m)
          (D.support seen base m) }

@[simp] theorem StaticWindowData.selector_q {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (seen : List (Fin n)) (m : Fin n)
    (base : StableBase P) :
    (D.selector seen m base).q = D.q m := rfl

@[simp] theorem StaticWindowData.selector_width {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (seen : List (Fin n)) (m : Fin n)
    (base : StableBase P) :
    upperBoundary (D.selector seen m base).window.upper -
        lowerBoundary (D.selector seen m base).window.lower =
      markerWindowWidth
        (leftMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m))
        (rightMarkerBits (D.enumeration m) base.1.toCore
          (listRevealed seen) (D.center base m)) := by
  exact nearest_window_width_eq_markerWindowWidth
    (D.enumeration m) base.1.toCore (listRevealed seen)
    (D.center base m) (D.window seen base m)

noncomputable def staticMarkerLog {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n)
    (revealed : Fin n → Prop) : ℝ := by
  classical
  exact Real.log (markerWindowWidth
    (leftMarkerBits (D.enumeration m) base.1.toCore revealed (D.center base m))
    (rightMarkerBits (D.enumeration m) base.1.toCore revealed (D.center base m)))

noncomputable def indexedStaticPathBudget {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (seen order : List (Fin n)) : ℝ :=
  (order.mapIdx fun k m ↦
    staticMarkerLog D base m (listRevealed (seen ++ order.take k))).sum

theorem prefixWindowPathBudget_static_eq_indexed {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (seen order : List (Fin n)) :
    prefixWindowPathBudget P D.selector base seen order =
      indexedStaticPathBudget D base seen order := by
  induction order generalizing seen with
  | nil => simp [prefixWindowPathBudget, indexedStaticPathBudget]
  | cons m ms ih =>
      simp only [prefixWindowPathBudget, indexedStaticPathBudget, List.mapIdx_cons,
        List.sum_cons]
      rw [D.selector_width seen m base]
      simp only [List.take_zero, List.append_nil, staticMarkerLog]
      rw [ih (seen := seen ++ [m])]
      congr 1
      unfold indexedStaticPathBudget
      apply congrArg List.sum
      simp only [List.mapIdx_eq_ofFn]
      apply congrArg List.ofFn
      funext i
      simp [List.take_succ_cons, List.append_assoc, staticMarkerLog]
      congr 4

noncomputable def lexTargetMarkerLog {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) (m : Fin n) : ℝ :=
  staticMarkerLog D base m (LexUnitRevealedBefore priority m)

noncomputable def lexTargetMarkerLogNN {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) (priority : Fin n → I) : ENNReal :=
  ENNReal.ofReal (lexTargetMarkerLog D base priority m)

def prefixPairWindowLogNN (leftLen rightLen : Nat)
    (v : (Fin leftLen → Bool) × (Fin rightLen → Bool)) : ENNReal :=
  ENNReal.ofReal (Real.log (markerWindowWidth
    (List.ofFn v.1) (List.ofFn v.2) : ℝ))

theorem measurable_prefixPairWindowLogNN (leftLen rightLen : Nat) :
    Measurable (prefixPairWindowLogNN leftLen rightLen) :=
  measurable_of_finite _

noncomputable def prefixPairWindowLog (leftLen rightLen : Nat)
    (v : (Fin leftLen → Bool) × (Fin rightLen → Bool)) : ℝ :=
  Real.log (markerWindowWidth (List.ofFn v.1) (List.ofFn v.2) : ℝ)

theorem measurable_prefixPairWindowLog (leftLen rightLen : Nat) :
    Measurable (prefixPairWindowLog leftLen rightLen) :=
  measurable_of_finite _

def lexMarkerPair {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (priority : Fin n → I) :
    (Fin j.val → Bool) × (Fin (q - (j.val + 1)) → Bool) :=
  ((fun i ↦ ownerMarkerBit E base
      (LexUnitRevealedBefore priority target) (leftMarkerIndex j i)),
    fun i ↦ ownerMarkerBit E base
      (LexUnitRevealedBefore priority target) (rightMarkerIndex j i))

theorem measurable_decide_lexBefore {n : Nat} (target p : Fin n) :
    Measurable (fun priority : Fin n → I ↦
      decide (LexUnitRevealedBefore priority target p)) := by
  change Measurable (fun priority : Fin n → I ↦
    if priority p < priority target ∨
      priority p = priority target ∧ p < target then true else false)
  have hpmeas : Measurable (fun priority : Fin n → I ↦ priority p) :=
    measurable_pi_apply p
  have htmeas : Measurable (fun priority : Fin n → I ↦ priority target) :=
    measurable_pi_apply target
  by_cases hpt : p < target
  · apply measurable_const.ite _ measurable_const
    convert (measurableSet_lt hpmeas htmeas).union
      (measurableSet_eq_fun
        (f := fun priority : Fin n → I ↦ priority p)
        (g := fun priority : Fin n → I ↦ priority target)
        hpmeas htmeas) using 1
    ext a
    simp [hpt]
  · apply measurable_const.ite _ measurable_const
    simpa only [hpt, and_false, or_false] using
      measurableSet_lt hpmeas htmeas

theorem measurable_lexMarkerPair {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q) :
    Measurable (lexMarkerPair E base j) := by
  apply Measurable.prod
  · exact measurable_pi_lambda _ fun i ↦ by
      simpa [lexMarkerPair, ownerMarkerBit] using
        measurable_decide_lexBefore target (stablePartnerOwner E base (leftMarkerIndex j i))
  · exact measurable_pi_lambda _ fun i ↦ by
      simpa [lexMarkerPair, ownerMarkerBit] using
        measurable_decide_lexBefore target (stablePartnerOwner E base (rightMarkerIndex j i))

theorem lexTargetMarkerLogNN_eq_prefixPair {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n)
    (priority : Fin n → I) :
    lexTargetMarkerLogNN D base m priority =
      prefixPairWindowLogNN (D.center base m).val
        (D.q m - ((D.center base m).val + 1))
        (lexMarkerPair (D.enumeration m) base.1.toCore
          (D.center base m) priority) := by
  unfold lexTargetMarkerLogNN lexTargetMarkerLog staticMarkerLog
    prefixPairWindowLogNN lexMarkerPair leftMarkerBits rightMarkerBits
  congr 4 <;> apply congrArg List.ofFn <;> funext i <;> congr 3

theorem lexTargetMarkerLog_eq_prefixPair {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n)
    (priority : Fin n → I) :
    lexTargetMarkerLog D base priority m =
      prefixPairWindowLog (D.center base m).val
        (D.q m - ((D.center base m).val + 1))
        (lexMarkerPair (D.enumeration m) base.1.toCore
          (D.center base m) priority) := by
  unfold lexTargetMarkerLog staticMarkerLog prefixPairWindowLog
    lexMarkerPair leftMarkerBits rightMarkerBits
  congr 4 <;> funext i <;> congr 3

theorem measurable_lexTargetMarkerLogNN {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n) :
    Measurable (lexTargetMarkerLogNN D base m) := by
  rw [funext fun priority ↦
    lexTargetMarkerLogNN_eq_prefixPair D base m priority]
  exact (measurable_prefixPairWindowLogNN _ _).comp
    (measurable_lexMarkerPair (D.enumeration m) base.1.toCore (D.center base m))

theorem measurable_lexTargetMarkerLog {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n) :
    Measurable (fun priority ↦ lexTargetMarkerLog D base priority m) := by
  rw [funext fun priority ↦
    lexTargetMarkerLog_eq_prefixPair D base m priority]
  exact (measurable_prefixPairWindowLog _ _).comp
    (measurable_lexMarkerPair (D.enumeration m) base.1.toCore (D.center base m))

theorem integrable_lexTargetMarkerLog {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P) (m : Fin n) :
    Integrable (fun priority ↦ lexTargetMarkerLog D base priority m)
      (FullPriorityMeasure n) := by
  let pairMap := lexMarkerPair (D.enumeration m) base.1.toCore (D.center base m)
  have hpair : Measurable pairMap :=
    measurable_lexMarkerPair (D.enumeration m) base.1.toCore (D.center base m)
  have hfun : AEStronglyMeasurable
      (prefixPairWindowLog (D.center base m).val
        (D.q m - ((D.center base m).val + 1)))
      ((FullPriorityMeasure n).map pairMap) :=
    (measurable_prefixPairWindowLog _ _).aestronglyMeasurable
  have hfinite : Integrable
      (prefixPairWindowLog (D.center base m).val
        (D.q m - ((D.center base m).val + 1)))
      ((FullPriorityMeasure n).map pairMap) := Integrable.of_finite
  have hcomp := (integrable_map_measure hfun hpair.aemeasurable).mp hfinite
  simpa only [Function.comp_def, pairMap,
    lexTargetMarkerLog_eq_prefixPair D base m] using hcomp

theorem ae_lexTargetMarkerLogNN_assemble_eq_actual {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) (x : I) :
    (fun ω ↦ lexTargetMarkerLogNN D base m
        (assemblePriority m (x, ω))) =ᵐ[TargetOtherPriorityMeasure m]
      (fun ω ↦ prefixPairWindowLogNN (D.center base m).val
        (D.q m - ((D.center base m).val + 1))
        (actualMarkerPair (D.enumeration m) base.1.toCore
          (D.center base m) (D.center_spec base m) x ω)) := by
  classical
  filter_upwards [ae_targetOther_all_ne m x] with ω hω
  rw [lexTargetMarkerLogNN_eq_prefixPair]
  apply congrArg (prefixPairWindowLogNN (D.center base m).val
    (D.q m - ((D.center base m).val + 1)))
  have hpred :
      LexUnitRevealedBefore (assemblePriority m (x, ω)) m =
        UnitRevealedBefore (assemblePriority m (x, ω)) m := by
    funext p
    apply propext
    by_cases hp : p = m
    · subst p
      simp [LexUnitRevealedBefore, UnitRevealedBefore]
    · have hne : ω (⟨p, hp⟩ : OtherMen m) ≠ x := hω ⟨p, hp⟩
      simp [LexUnitRevealedBefore, UnitRevealedBefore,
        assemblePriority_other m p (x, ω) hp, assemblePriority_target,
        hne]
  unfold lexMarkerPair actualMarkerPair
  apply Prod.ext
  · funext i
    calc
      ownerMarkerBit (D.enumeration m) base.1.toCore
          (LexUnitRevealedBefore (assemblePriority m (x, ω)) m)
          (leftMarkerIndex (D.center base m) i) =
          ownerMarkerBit (D.enumeration m) base.1.toCore
            (UnitRevealedBefore (assemblePriority m (x, ω)) m)
            (leftMarkerIndex (D.center base m) i) := by
        rw [Bool.eq_iff_iff]
        simp only [ownerMarkerBit_eq_true_iff]
        exact iff_of_eq (congrFun hpred
          (stablePartnerOwner (D.enumeration m) base.1.toCore
            (leftMarkerIndex (D.center base m) i)))
      _ = _ := ownerMarkerBit_split_eq_indicator
        (D.enumeration m) base.1.toCore (D.center base m)
        (D.center_spec base m) x ω (Sum.inl i)
  · funext i
    calc
      ownerMarkerBit (D.enumeration m) base.1.toCore
          (LexUnitRevealedBefore (assemblePriority m (x, ω)) m)
          (rightMarkerIndex (D.center base m) i) =
          ownerMarkerBit (D.enumeration m) base.1.toCore
            (UnitRevealedBefore (assemblePriority m (x, ω)) m)
            (rightMarkerIndex (D.center base m) i) := by
        rw [Bool.eq_iff_iff]
        simp only [ownerMarkerBit_eq_true_iff]
        exact iff_of_eq (congrFun hpred
          (stablePartnerOwner (D.enumeration m) base.1.toCore
            (rightMarkerIndex (D.center base m) i)))
      _ = _ := ownerMarkerBit_split_eq_indicator
        (D.enumeration m) base.1.toCore (D.center base m)
        (D.center_spec base m) x ω (Sum.inr i)

theorem indexedStaticPathBudget_priorityOrder_eq_sum {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) :
    indexedStaticPathBudget D base [] (List.ofFn (priorityOrder priority)) =
      ∑ m : Fin n, lexTargetMarkerLog D base priority m := by
  classical
  unfold indexedStaticPathBudget
  let order := priorityOrder priority
  have hmap :
      (List.ofFn order).mapIdx (fun k m ↦
        staticMarkerLog D base m
          (listRevealed ([] ++ (List.ofFn order).take k))) =
        List.ofFn (fun i : Fin n ↦
          staticMarkerLog D base (order i)
            (listRevealed ((List.ofFn order).take i.val))) := by
    apply List.ext_get
    · simp
    · intro k hk hk'
      simp
  rw [show List.ofFn (priorityOrder priority) = List.ofFn order by rfl]
  rw [hmap, List.sum_ofFn]
  have hpoint : ∀ i : Fin n,
      staticMarkerLog D base (order i)
          (listRevealed ((List.ofFn order).take i.val)) =
        lexTargetMarkerLog D base priority (order i) := by
    intro i
    unfold lexTargetMarkerLog
    congr 1
    funext p
    apply propext
    rw [show listRevealed ((List.ofFn order).take i.val) p ↔
        p ∈ (List.ofFn order).take i.val by rfl]
    rw [mem_take_ofFn_perm_iff]
    have hi : (order.symm (order i)).val = i.val := by simp
    rw [← hi]
    exact fixedOrderRevealed_priorityOrder_target_iff
      priority (order i) p
  have hsum :
      (∑ i : Fin n, staticMarkerLog D base (order i)
        (listRevealed ((List.ofFn order).take i.val))) =
        ∑ m : Fin n, lexTargetMarkerLog D base priority m := by
    calc
      _ = ∑ i : Fin n, lexTargetMarkerLog D base priority (order i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpoint i
      _ = _ := Equiv.sum_comp order (lexTargetMarkerLog D base priority)
  exact hsum

theorem prefixWindowPathBudget_priorityOrder_eq_sum {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) :
    prefixWindowPathBudget P D.selector base []
        (List.ofFn (priorityOrder priority)) =
      ∑ m : Fin n, lexTargetMarkerLog D base priority m := by
  rw [prefixWindowPathBudget_static_eq_indexed]
  exact indexedStaticPathBudget_priorityOrder_eq_sum D base priority

/-! The analytic certificate is stated on `ℝ`; this is the exact bridge
from the outer unit-interval probability coordinate, including the harmless
left endpoint. -/
theorem integral_unitInterval_eq_Ioc (f : ℝ → ℝ) :
    (∫ x : I, f (x : ℝ) ∂volume) =
      ∫ x : ℝ in Set.Ioc (0 : ℝ) 1, f x := by
  rw [unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe f]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

theorem lintegral_unitInterval_eq_Ioc (f : ℝ → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x : I, f (x : ℝ) ∂volume) =
      ∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1, f x := by
  rw [unitInterval.measurePreserving_coe.lintegral_comp hf]
  rw [← restrict_Ioc_eq_restrict_Icc]

def geometricWindowLogNN (z : Nat × Nat) : ENNReal :=
  ENNReal.ofReal (Real.log (geometricWindow z : ℝ))

theorem measurable_geometricWindow : Measurable geometricWindow :=
  measurable_of_countable _

theorem measurable_geometricWindowLogNN : Measurable geometricWindowLogNN :=
  measurable_of_countable _

/-- Exact fixed-threshold geometric expectation, first in `ENNReal`.  This is
the missing pushforward/fiber bridge between the shared dummy coupling and
the analytic series. -/
theorem lintegral_geometricWindowLogNN_eq_tsum {x : I} (hx : x ≠ 0) :
    (∫⁻ z, geometricWindowLogNN z ∂(GeometricPairMeasure x)) =
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  unfold geometricWindowLogNN
  rw [← MeasureTheory.lintegral_map
    (f := fun k : Nat ↦ ENNReal.ofReal (Real.log (k : ℝ)))
    (g := geometricWindow) (measurable_of_countable _)
    measurable_geometricWindow]
  rw [MeasureTheory.lintegral_countable']
  apply tsum_congr
  intro k
  rw [Measure.map_apply measurable_geometricWindow (measurableSet_singleton k)]
  change ENNReal.ofReal (Real.log (k : ℝ)) *
      (GeometricPairMeasure x) {z : Nat × Nat | geometricWindow z = k} = _
  have hmassReal := geometricWindow_real_fiber hx k
  have hmass :
      (GeometricPairMeasure x) {z : Nat × Nat | geometricWindow z = k} =
        ENNReal.ofReal ((k : ℝ) * ((x : ℝ) ^ 2 *
          (1 - (x : ℝ)) ^ (k - 1))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
  rw [hmass, ← ENNReal.ofReal_mul (Real.log_natCast_nonneg k)]
  congr 1
  simp only [geometricLogTerm]
  ring

theorem measurable_actualMarkerPair {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (x : I) : Measurable (actualMarkerPair E base j hbaseTarget x) := by
  apply Measurable.prod
  · exact measurable_pi_lambda _ fun i ↦
      measurable_actualMarkerBit E base j hbaseTarget x (Sum.inl i)
  · exact measurable_pi_lambda _ fun i ↦
      measurable_actualMarkerBit E base j hbaseTarget x (Sum.inr i)

theorem ofFn_streamPrefixVector (m : Nat) (b : Nat → Bool) :
    List.ofFn (streamPrefixVector m b) = streamPrefix m b := by
  apply List.ext_get
  · simp [streamPrefix]
  · intro i hi hi'
    simp [streamPrefix, streamPrefixVector]

/-- A genuine finite pair of marker scans is bounded in expectation by the
two infinite geometric waiting times on the *same* dummy sample. -/
theorem lintegral_actualMarkerPair_le_geometric {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    {x : I} (hx : x ≠ 0) :
    (∫⁻ ω, prefixPairWindowLogNN j.val (q - (j.val + 1))
        (actualMarkerPair E base j hbaseTarget x ω)
      ∂(TargetOtherPriorityMeasure target)) ≤
      ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
        ∂(InfiniteDummyPairMeasure x) := by
  calc
    _ = ∫⁻ v, prefixPairWindowLogNN j.val (q - (j.val + 1)) v
          ∂((TargetOtherPriorityMeasure target).map
            (actualMarkerPair E base j hbaseTarget x)) := by
      symm
      exact MeasureTheory.lintegral_map
        (measurable_prefixPairWindowLogNN _ _)
        (measurable_actualMarkerPair E base j hbaseTarget x)
    _ = ∫⁻ v, prefixPairWindowLogNN j.val (q - (j.val + 1)) v
          ∂((InfiniteDummyPairMeasure x).map
            (pairedPrefixVector j.val (q - (j.val + 1)))) := by
      rw [map_actualMarkerPair_eq_pairedPrefixVector E base j hbaseTarget x]
    _ = ∫⁻ z, prefixPairWindowLogNN j.val (q - (j.val + 1))
          (pairedPrefixVector j.val (q - (j.val + 1)) z)
          ∂(InfiniteDummyPairMeasure x) := by
      exact MeasureTheory.lintegral_map
        (measurable_prefixPairWindowLogNN _ _)
        (measurable_pairedPrefixVector _ _)
    _ ≤ _ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_markerWindowWidth_prefix_le_geometricWindow hx
        j.val (q - (j.val + 1))] with z hz
      apply ENNReal.ofReal_le_ofReal
      apply Real.log_le_log
      · have hl := truncatedWait_pos (streamPrefix j.val z.1)
        have hr := truncatedWait_pos
          (streamPrefix (q - (j.val + 1)) z.2)
        exact_mod_cast (show 0 < markerWindowWidth
          (streamPrefix j.val z.1)
          (streamPrefix (q - (j.val + 1)) z.2) by
            simp only [markerWindowWidth]
            omega)
      · simpa [prefixPairWindowLogNN, pairedPrefixVector,
          ofFn_streamPrefixVector] using hz

theorem lintegral_actualMarkerPair_le_geometricSeries {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    {x : I} (hx : x ≠ 0) :
    (∫⁻ ω, prefixPairWindowLogNN j.val (q - (j.val + 1))
        (actualMarkerPair E base j hbaseTarget x ω)
      ∂(TargetOtherPriorityMeasure target)) ≤
      ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) := by
  calc
    _ ≤ ∫⁻ z, geometricWindowLogNN (infiniteDummyWaitPair z)
        ∂(InfiniteDummyPairMeasure x) :=
      lintegral_actualMarkerPair_le_geometric E base j hbaseTarget hx
    _ = ∫⁻ p, geometricWindowLogNN p
        ∂((InfiniteDummyPairMeasure x).map infiniteDummyWaitPair) := by
      symm
      exact MeasureTheory.lintegral_map measurable_geometricWindowLogNN
        measurable_infiniteDummyWaitPair
    _ = ∫⁻ p, geometricWindowLogNN p ∂(GeometricPairMeasure x) := by
      rw [infiniteDummyWaitPair_has_geometric_pair_law hx]
    _ = _ := lintegral_geometricWindowLogNN_eq_tsum hx

theorem lintegral_unit_geometricSeries_lt_log_seventeen_div_five :
    (∫⁻ x : I,
        ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k (x : ℝ)) ∂volume) <
      ENNReal.ofReal (Real.log ((17 : ℝ) / 5)) := by
  let F : ℝ → ENNReal := fun x ↦
    ∑' k : Nat, ENNReal.ofReal (geometricLogTerm k x)
  have hF : Measurable F := by
    exact Measurable.tsum fun k ↦
      (geometricLogTerm_continuous k).measurable.ennreal_ofReal
  change (∫⁻ x : I, F (x : ℝ) ∂volume) < _
  rw [lintegral_unitInterval_eq_Ioc F hF]
  rw [show (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1, F x) =
      ∑' k : Nat, ENNReal.ofReal (geometricLogWeight k) by
    exact lintegral_tsum_geometric_log_term]
  rw [← ENNReal.ofReal_tsum_of_nonneg geometricLogWeight_nonneg
    summable_geometricLogWeight]
  apply (ENNReal.ofReal_lt_ofReal_iff (Real.log_pos (by norm_num))).2
  exact geometricLogSeries_lt_log_seventeen_div_five

theorem lintegral_unit_actualMarkerPair_lt_log_seventeen_div_five {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (j : Fin q)
    (hbaseTarget : base.manPartner target = E.ranked.partner j) :
    (∫⁻ x : I, ∫⁻ ω,
        prefixPairWindowLogNN j.val (q - (j.val + 1))
          (actualMarkerPair E base j hbaseTarget x ω)
        ∂(TargetOtherPriorityMeasure target) ∂volume) <
      ENNReal.ofReal (Real.log ((17 : ℝ) / 5)) := by
  apply lt_of_le_of_lt _
    lintegral_unit_geometricSeries_lt_log_seventeen_div_five
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [MeasureTheory.volume.ae_ne (0 : I)] with x hx
  exact lintegral_actualMarkerPair_le_geometricSeries
    E base j hbaseTarget hx

theorem lintegral_full_lexTargetMarkerLogNN_lt {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) :
    (∫⁻ priority, lexTargetMarkerLogNN D base m priority
      ∂(FullPriorityMeasure n)) <
      ENNReal.ofReal (Real.log ((17 : ℝ) / 5)) := by
  calc
    _ = ∫⁻ z, lexTargetMarkerLogNN D base m
          (assemblePriority m z) ∂(SplitTargetPriorityMeasure m) := by
      rw [← map_assemblePriority_splitTargetPriorityMeasure m]
      exact MeasureTheory.lintegral_map
        (measurable_lexTargetMarkerLogNN D base m)
        (measurable_assemblePriority m)
    _ = ∫⁻ x : I, ∫⁻ ω,
          lexTargetMarkerLogNN D base m (assemblePriority m (x, ω))
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      exact MeasureTheory.lintegral_prod _
        ((measurable_lexTargetMarkerLogNN D base m).comp
          (measurable_assemblePriority m)).aemeasurable
    _ = ∫⁻ x : I, ∫⁻ ω,
          prefixPairWindowLogNN (D.center base m).val
            (D.q m - ((D.center base m).val + 1))
            (actualMarkerPair (D.enumeration m) base.1.toCore
              (D.center base m) (D.center_spec base m) x ω)
          ∂(TargetOtherPriorityMeasure m) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro x
      exact MeasureTheory.lintegral_congr_ae
        (ae_lexTargetMarkerLogNN_assemble_eq_actual D base m x)
    _ < _ := lintegral_unit_actualMarkerPair_lt_log_seventeen_div_five
      (D.enumeration m) base.1.toCore (D.center base m)
      (D.center_spec base m)

theorem lexTargetMarkerLog_nonneg {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : StableBase P)
    (priority : Fin n → I) (m : Fin n) :
    0 ≤ lexTargetMarkerLog D base priority m := by
  rw [lexTargetMarkerLog_eq_prefixPair]
  exact Real.log_natCast_nonneg _

theorem integral_full_lexTargetMarkerLog_lt {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (base : StableBase P)
    (m : Fin n) :
    (∫ priority, lexTargetMarkerLog D base priority m
      ∂(FullPriorityMeasure n)) < Real.log ((17 : ℝ) / 5) := by
  apply (ENNReal.ofReal_lt_ofReal_iff (Real.log_pos (by norm_num))).1
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_lexTargetMarkerLog D base m)
    (Filter.Eventually.of_forall fun priority ↦
      lexTargetMarkerLog_nonneg D base priority m)]
  change (∫⁻ priority, lexTargetMarkerLogNN D base m priority
    ∂(FullPriorityMeasure n)) < _
  exact lintegral_full_lexTargetMarkerLogNN_lt D base m

noncomputable def aggregateLexCost {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I) : ℝ :=
  ((stableSet P).card : ℝ)⁻¹ *
    ∑ base ∈ stableSet P,
      ∑ m : Fin n,
        if h : Stable P base then
          lexTargetMarkerLog D ⟨base, h⟩ priority m
        else 0

theorem uniformPrefixWindowExpectation_priority_eq_aggregate {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (priority : Fin n → I) :
    uniformPrefixWindowExpectation P D.selector
        (List.ofFn (priorityOrder priority)) =
      aggregateLexCost D priority := by
  classical
  unfold uniformPrefixWindowExpectation aggregateLexCost
  congr 1
  apply Finset.sum_congr rfl
  intro base hbase
  have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
  simp only [prefixWindowPathBudgetOrZero, hs, dif_pos]
  exact prefixWindowPathBudget_priorityOrder_eq_sum D
    (⟨base, hs⟩ : StableBase P) priority

theorem log_stableCount_le_aggregateLexCost {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (priority : Fin n → I)
    (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) ≤ aggregateLexCost D priority := by
  rw [← uniformPrefixWindowExpectation_priority_eq_aggregate D priority]
  exact log_stableCount_le_priorityWindowExpectation
    P D.selector priority hstable

noncomputable def stableBaseLexCost {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : MatchingCode n)
    (priority : Fin n → I) : ℝ :=
  if h : Stable P base then
    ∑ m : Fin n, lexTargetMarkerLog D ⟨base, h⟩ priority m
  else 0

theorem integrable_stableBaseLexCost {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (base : MatchingCode n) :
    Integrable (stableBaseLexCost D base) (FullPriorityMeasure n) := by
  classical
  by_cases h : Stable P base
  · rw [show stableBaseLexCost D base = fun priority ↦
        ∑ m : Fin n, lexTargetMarkerLog D ⟨base, h⟩ priority m by
      funext priority
      simp [stableBaseLexCost, h]]
    exact integrable_finsetSum (Finset.univ : Finset (Fin n))
      (fun m _ ↦ integrable_lexTargetMarkerLog D ⟨base, h⟩ m)
  · rw [show stableBaseLexCost D base = fun _ ↦ (0 : ℝ) by
      funext priority
      simp [stableBaseLexCost, h]]
    exact integrable_const 0

theorem aggregateLexCost_eq_stableBaseLexCost_sum {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P) (priority : Fin n → I) :
    aggregateLexCost D priority =
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, stableBaseLexCost D base priority := by
  classical
  unfold aggregateLexCost
  congr 1
  apply Finset.sum_congr rfl
  intro base hbase
  have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
  simp [stableBaseLexCost, hs]

theorem integrable_aggregateLexCost {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) :
    Integrable (aggregateLexCost D) (FullPriorityMeasure n) := by
  rw [show aggregateLexCost D = fun priority ↦
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, stableBaseLexCost D base priority by
    funext priority
    exact aggregateLexCost_eq_stableBaseLexCost_sum D priority]
  apply Integrable.const_mul
  exact integrable_finsetSum (stableSet P) fun base _ ↦
    integrable_stableBaseLexCost D base

theorem integral_stableBaseLexCost_of_stable {n : Nat}
    {P : ProfileCode n} (D : StaticWindowData P)
    (base : MatchingCode n) (hbase : Stable P base) :
    (∫ priority, stableBaseLexCost D base priority
      ∂(FullPriorityMeasure n)) =
      ∑ m : Fin n, ∫ priority,
        lexTargetMarkerLog D ⟨base, hbase⟩ priority m
        ∂(FullPriorityMeasure n) := by
  rw [show stableBaseLexCost D base = fun priority ↦
      ∑ m : Fin n, lexTargetMarkerLog D ⟨base, hbase⟩ priority m by
    funext priority
    simp [stableBaseLexCost, hbase]]
  exact MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin n))
    (fun m _ ↦ integrable_lexTargetMarkerLog D ⟨base, hbase⟩ m)

theorem integral_aggregateLexCost_eq {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) :
    (∫ priority, aggregateLexCost D priority
      ∂(FullPriorityMeasure n)) =
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n) := by
  classical
  rw [show aggregateLexCost D = fun priority ↦
      ((stableSet P).card : ℝ)⁻¹ *
        ∑ base ∈ stableSet P, stableBaseLexCost D base priority by
    funext priority
    exact aggregateLexCost_eq_stableBaseLexCost_sum D priority]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum (stableSet P)
    (fun base _ ↦ integrable_stableBaseLexCost D base)]
  congr 1
  apply Finset.sum_congr rfl
  intro base hbase
  have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
  rw [integral_stableBaseLexCost_of_stable D base hs]
  apply Finset.sum_congr rfl
  intro m _
  simp [hs]

theorem integral_stableBaseLexCost_lt {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hn : 1 ≤ n) (base : MatchingCode n)
    (hbase : Stable P base) :
    (∫ priority, stableBaseLexCost D base priority
      ∂(FullPriorityMeasure n)) <
      (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
  rw [integral_stableBaseLexCost_of_stable D base hbase]
  calc
    (∑ m : Fin n, ∫ priority,
        lexTargetMarkerLog D ⟨base, hbase⟩ priority m
        ∂(FullPriorityMeasure n)) <
        ∑ _m : Fin n, Real.log ((17 : ℝ) / 5) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, Nat.zero_lt_of_lt hn⟩, Finset.mem_univ _⟩
      · intro m _
        exact integral_full_lexTargetMarkerLog_lt D ⟨base, hbase⟩ m
    _ = (n : ℝ) * Real.log ((17 : ℝ) / 5) := by simp

theorem integral_aggregateLexCost_lt {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hn : 1 ≤ n)
    (hstable : (stableSet P).Nonempty) :
    (∫ priority, aggregateLexCost D priority
      ∂(FullPriorityMeasure n)) <
      (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
  classical
  rw [integral_aggregateLexCost_eq D]
  have hcard : 0 < ((stableSet P).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hstable)
  have hsum :
      (∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n)) <
        ∑ _base ∈ stableSet P,
          (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
    apply Finset.sum_lt_sum_of_nonempty hstable
    intro base hbase
    have hs : Stable P base := (mem_stableSet_iff P base).1 hbase
    simpa [hs, integral_stableBaseLexCost_of_stable] using
      integral_stableBaseLexCost_lt D hn base hs
  calc
    ((stableSet P).card : ℝ)⁻¹ *
        (∑ base ∈ stableSet P,
          ∑ m : Fin n, ∫ priority,
            if h : Stable P base then
              lexTargetMarkerLog D ⟨base, h⟩ priority m
            else 0
            ∂(FullPriorityMeasure n)) <
      ((stableSet P).card : ℝ)⁻¹ *
        (∑ _base ∈ stableSet P,
          (n : ℝ) * Real.log ((17 : ℝ) / 5)) :=
      mul_lt_mul_of_pos_left hsum (inv_pos.mpr hcard)
    _ = (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

theorem log_stableCount_lt_of_nonempty {n : Nat} {P : ProfileCode n}
    (D : StaticWindowData P) (hn : 1 ≤ n)
    (hstable : (stableSet P).Nonempty) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
  have hmono : Real.log (stableCount P) ≤
      ∫ priority, aggregateLexCost D priority
        ∂(FullPriorityMeasure n) := by
    have h := MeasureTheory.integral_mono
      (integrable_const (Real.log (stableCount P)) :
        Integrable (fun _ : Fin n → I ↦ Real.log (stableCount P))
          (FullPriorityMeasure n))
      (integrable_aggregateLexCost D)
      (fun priority ↦ log_stableCount_le_aggregateLexCost D priority hstable)
    simpa using h
  exact lt_of_le_of_lt hmono
    (integral_aggregateLexCost_lt D hn hstable)

/-- The public logarithmic profile bound.  The empty-count branch is explicit:
`log 0 = 0`, while the claimed right-hand side is positive for `n ≥ 1`. -/
theorem log_stableCount_lt_n_log_seventeen_fifths (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    Real.log (stableCount P) <
      (n : ℝ) * Real.log ((17 : ℝ) / 5) := by
  classical
  by_cases hz : stableCount P = 0
  · rw [hz]
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_pos (by exact_mod_cast hn)
      (Real.log_pos (by norm_num))
  · have hpos : 0 < stableCount P := Nat.pos_of_ne_zero hz
    have hstable : (stableSet P).Nonempty := by
      apply Finset.card_pos.mp
      simpa [stableCount] using hpos
    let D : StaticWindowData P := Classical.choice (exists_staticWindowData P)
    exact log_stableCount_lt_of_nonempty D hn hstable

/-- Exact kernel-facing bound for every coded strict complete profile. -/
theorem stableCount_nat_bound_seventeen_fifths (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    5 ^ n * stableCount P < 17 ^ n := by
  by_cases hz : stableCount P = 0
  · rw [hz, mul_zero]
    exact zero_lt_nat_target_17_final
  · exact log_lt_to_nat_crossmul_17_5_final (Nat.pos_of_ne_zero hz)
      (log_stableCount_lt_n_log_seventeen_fifths n hn P)

/-- Exact bound for the maximum number of stable matchings. -/
theorem SM_nat_bound_seventeen_fifths (n : Nat) (hn : 1 ≤ n) :
    5 ^ n * SM n < 17 ^ n := by
  apply SM_nat_bound_of_all_profiles n
  exact fun P ↦ stableCount_nat_bound_seventeen_fifths n hn P

/-- Real-valued exponential bound for each profile. -/
theorem stableCount_lt_seventeen_fifths_pow (n : Nat)
    (hn : 1 ≤ n) (P : ProfileCode n) :
    (stableCount P : ℝ) < ((17 : ℝ) / 5) ^ n :=
  stableCount_lt_seventeen_fifths_pow_of_nat_bound n P
    (stableCount_nat_bound_seventeen_fifths n hn P)

/-- Real-valued exponential bound for the extremal function `SM`. -/
theorem SM_lt_seventeen_fifths_pow (n : Nat) (hn : 1 ≤ n) :
    (SM n : ℝ) < ((17 : ℝ) / 5) ^ n :=
  SM_lt_seventeen_fifths_pow_of_nat_bound n
    (SM_nat_bound_seventeen_fifths n hn)

end

end StableMatchingsE2E
