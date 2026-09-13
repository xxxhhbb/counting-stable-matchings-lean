import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace StableMatchingsJointCharging

open scoped BigOperators

/-! ## Poset deletion facts -/

def IsFinsetIdeal {R : Type*} [PartialOrder R] (D : Finset R) : Prop :=
  ∀ ⦃x y : R⦄, x ≤ y → y ∈ D → x ∈ D

def IsMaximalIn {R : Type*} [PartialOrder R] (D : Finset R) (r : R) : Prop :=
  r ∈ D ∧ ∀ ⦃s : R⦄, s ∈ D → r ≤ s → s = r

def IsMinimalOutside {R : Type*} [PartialOrder R]
    (D : Finset R) (r : R) : Prop :=
  r ∉ D ∧ ∀ ⦃s : R⦄, s < r → s ∈ D

/-- Removing any subset of maximal elements from a finite downset leaves a
downset. -/
theorem ideal_sdiff_maximal_subset
    {R : Type*} [PartialOrder R] [DecidableEq R]
    (D A : Finset R) (hD : IsFinsetIdeal D)
    (_hAD : A ⊆ D)
    (hmax : ∀ r ∈ A, IsMaximalIn D r) :
    IsFinsetIdeal (D \ A) := by
  intro x y hxy hy
  have hyD : y ∈ D := (Finset.mem_sdiff.mp hy).1
  have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
  have hxD : x ∈ D := hD hxy hyD
  apply Finset.mem_sdiff.mpr ⟨hxD, ?_⟩
  intro hxA
  have heq : y = x := (hmax x hxA).2 hyD hxy
  subst y
  exact hyA hxA

/-- Every removed maximal element becomes minimal outside the deletion image. -/
theorem removed_maximal_is_minimal_outside
    {R : Type*} [PartialOrder R] [DecidableEq R]
    (D A : Finset R) (hD : IsFinsetIdeal D)
    (hAD : A ⊆ D)
    (hmax : ∀ r ∈ A, IsMaximalIn D r)
    {r : R} (hrA : r ∈ A) :
    IsMinimalOutside (D \ A) r := by
  constructor
  · simp [hrA]
  · intro s hsr
    have hrD : r ∈ D := hAD hrA
    have hsD : s ∈ D := hD hsr.le hrD
    apply Finset.mem_sdiff.mpr ⟨hsD, ?_⟩
    intro hsA
    have heq : r = s := (hmax s hsA).2 hrD hsr.le
    exact hsr.ne heq.symm

/-- The deletion image and the original frontier recover the removed subset
exactly; hence they recover the original ideal. -/
theorem recover_deleted_subset
    {R : Type*} [DecidableEq R]
    (D L A : Finset R) (hAL : A ⊆ L) (hLD : L ⊆ D) :
    L \ (D \ A) = A := by
  ext r
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hrL, hnot⟩
    by_contra hrA
    exact hnot ⟨hLD hrL, hrA⟩
  · intro hrA
    exact ⟨hAL hrA, fun h ↦ h.2 hrA⟩

theorem recover_deleted_ideal
    {R : Type*} [DecidableEq R]
    (D A : Finset R) (hAD : A ⊆ D) :
    (D \ A) ∪ A = D := by
  ext r
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hrD, -⟩ | hrA)
    · exact hrD
    · exact hAD hrA
  · intro hrD
    by_cases hrA : r ∈ A
    · exact Or.inr hrA
    · exact Or.inl ⟨hrD, hrA⟩

/-! ## Participant-chain boundary uniqueness -/

theorem maximal_in_participant_chain_unique
    {R : Type*} [PartialOrder R] {D : Finset R}
    (involves : R → Prop)
    (hchain : ∀ ⦃r s : R⦄, involves r → involves s → r ≤ s ∨ s ≤ r)
    {r s : R} (hrv : involves r) (hsv : involves s)
    (hr : IsMaximalIn D r) (hs : IsMaximalIn D s) :
    r = s := by
  rcases hchain hrv hsv with hrs | hsr
  · exact (hr.2 hs.1 hrs).symm
  · exact hs.2 hr.1 hsr

theorem minimal_outside_participant_chain_unique
    {R : Type*} [PartialOrder R] {D : Finset R}
    (involves : R → Prop)
    (hchain : ∀ ⦃r s : R⦄, involves r → involves s → r ≤ s ∨ s ≤ r)
    {r s : R} (hrv : involves r) (hsv : involves s)
    (hr : IsMinimalOutside D r) (hs : IsMinimalOutside D s) :
    r = s := by
  rcases hchain hrv hsv with hrs | hsr
  · rcases hrs.eq_or_lt with rfl | hrslt
    · rfl
    · exact False.elim (hr.1 (hs.2 hrslt))
  · rcases hsr.eq_or_lt with hsrEq | hsrlt
    · exact hsrEq.symm
    · exact False.elim (hs.1 (hr.2 hsrlt))

/-- A maximal included element and a minimal excluded element that are
comparable must occur in the included-to-excluded order. -/
theorem maximal_in_lt_minimal_outside_of_comparable
    {R : Type*} [PartialOrder R] {D : Finset R} {r s : R}
    (hD : IsFinsetIdeal D)
    (hr : IsMaximalIn D r) (hs : IsMinimalOutside D s)
    (hcomp : r ≤ s ∨ s ≤ r) :
    r < s := by
  rcases hcomp with hrs | hsr
  · exact lt_of_le_of_ne hrs (fun h ↦ hs.1 (h ▸ hr.1))
  · exact False.elim (hs.1 (hD hsr hr.1))

/-- Such a boundary pair is a cover relation: there is no poset element
strictly between it.  This is the order-theoretic part of the no-parallel
boundary-edge argument. -/
theorem no_between_maximal_in_minimal_outside
    {R : Type*} [PartialOrder R] {D : Finset R} {r s t : R}
    (hr : IsMaximalIn D r) (hs : IsMinimalOutside D s)
    (hrt : r < t) (hts : t < s) :
    False := by
  have htD : t ∈ D := hs.2 hts
  have htr : t = r := hr.2 htD hrt.le
  exact hrt.ne htr.symm

/-- If rotations involving one participant form a chain, a maximal-in and a
minimal-out rotation involving that participant are consecutive across the
ideal boundary. -/
theorem participant_boundary_is_cover
    {R : Type*} [PartialOrder R] {D : Finset R}
    (involves : R → Prop)
    (hchain : ∀ ⦃r s : R⦄, involves r → involves s → r ≤ s ∨ s ≤ r)
    {r s : R} (hrv : involves r) (hsv : involves s)
    (hD : IsFinsetIdeal D)
    (hr : IsMaximalIn D r) (hs : IsMinimalOutside D s) :
    r < s ∧ ¬ ∃ t : R, r < t ∧ t < s := by
  have hrs := maximal_in_lt_minimal_outside_of_comparable hD hr hs (hchain hrv hsv)
  exact ⟨hrs, by
    rintro ⟨t, hrt, hts⟩
    exact no_between_maximal_in_minimal_outside hr hs hrt hts⟩

/-- Each bad ideal with at least `r` deletable frontier rotations contributes
at least `2^r` deletion pairs.  This is the exact finite lower-counting half
of the boundary-deletion argument. -/
theorem deletion_pair_count_lower
    {D R : Type*} [DecidableEq D] [DecidableEq R]
    (bad : Finset D) (frontier : D → Finset R) (r : ℕ)
    (hfrontier : ∀ d ∈ bad, r ≤ (frontier d).card) :
    bad.card * 2 ^ r ≤
      ∑ d ∈ bad, (frontier d).powerset.card := by
  calc
    bad.card * 2 ^ r = ∑ _d ∈ bad, 2 ^ r := by simp
    _ ≤ ∑ d ∈ bad, 2 ^ (frontier d).card := by
      exact Finset.sum_le_sum fun d hd ↦
        pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (hfrontier d hd)
    _ = ∑ d ∈ bad, (frontier d).powerset.card := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.card_powerset]

/-- A uniform bound on all fibers of a finite map gives the standard global
domain-cardinality bound.  In the application, the map sends a deletion pair
`(D,A)` to its image ideal `J`, and `Q` is the boundary-matching budget. -/
theorem card_le_card_mul_of_fiber_card_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (Q : ℕ)
    (hfiber : ∀ y : Y,
      ((Finset.univ : Finset X).filter fun x ↦ f x = y).card ≤ Q) :
    Fintype.card X ≤ Fintype.card Y * Q := by
  classical
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Y))
    (f := f) (by simp)]
  calc
    (∑ y ∈ (Finset.univ : Finset Y),
        ((Finset.univ : Finset X).filter fun x ↦ f x = y).card) ≤
        ∑ _y ∈ (Finset.univ : Finset Y), Q := by
      exact Finset.sum_le_sum fun y _ ↦ hfiber y
    _ = Fintype.card Y * Q := by simp

/-- Arithmetic closing step for a deletion double count.  `bad * 2^r` is the
lower count of deletion pairs, while `total * Q` is the fixed-image fiber
upper count.  If every deletion fiber budget `Q` is at most half the lower
factor, at most half of all ideals can be bad. -/
theorem deletion_double_count_half
    (bad total Q r : ℕ) (hQ : 0 < Q)
    (hcount : bad * 2 ^ r ≤ total * Q)
    (hhalf : 2 * Q ≤ 2 ^ r) :
    2 * bad ≤ total := by
  have hmul : (2 * bad) * Q ≤ total * Q := by
    calc
      (2 * bad) * Q = bad * (2 * Q) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ bad * 2 ^ r := Nat.mul_le_mul_left bad hhalf
      _ ≤ total * Q := hcount
  exact le_of_mul_le_mul_right hmul hQ

/-- Integer form of the expectation step: if at most half of `M` objects are
bad and every good object has charge at least `r`, then the total charge is
at least `M*r/2`. -/
theorem total_charge_half_lower
    (M bad r totalCharge : ℕ)
    (hbad : 2 * bad ≤ M)
    (hcharge : (M - bad) * r ≤ totalCharge) :
    M * r ≤ 2 * totalCharge := by
  have hgood : M ≤ 2 * (M - bad) := by omega
  calc
    M * r ≤ (2 * (M - bad)) * r := Nat.mul_le_mul_right r hgood
    _ = 2 * ((M - bad) * r) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ 2 * totalCharge := Nat.mul_le_mul_left 2 hcharge

end StableMatchingsJointCharging
