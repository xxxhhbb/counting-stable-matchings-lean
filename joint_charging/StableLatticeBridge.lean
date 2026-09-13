import Mathlib.Order.Birkhoff
import StableMatchingsE2E.ProfileCode
import StableMatchings355.FiniteJoin
import «BoundaryDeletionCore»

/-!
# The finite lattice of stable matchings of a coded profile

This file builds the profile-level object needed before Birkhoff
sup-irreducibles can be used as canonical rotations.  The order is oriented
so that `mu ≤ nu` means every man weakly prefers `nu` to `mu`; hence the
men-better pointwise operation is `sup` and the men-worse operation is `inf`.
-/

namespace StableMatchingsJointCharging

open StableMatchings355 StableMatchingsE2E

noncomputable section

abbrev CodedStable {n : Nat} (P : ProfileCode n) :=
  {mu : MatchingCode n // Stable P mu}

/-- Exchange the two sides of a strict complete profile. -/
def transposeProfile {n : Nat} (P : Profile (Fin n) (Fin n)) :
    Profile (Fin n) (Fin n) where
  manPref := P.womanPref
  womanPref := P.manPref
  man_decidable := P.woman_decidable
  woman_decidable := P.man_decidable
  man_asymm := P.woman_asymm
  woman_asymm := P.man_asymm
  man_trans := P.woman_trans
  woman_trans := P.man_trans
  man_total := P.woman_total
  woman_total := P.man_total

/-- Exchange the two partner maps of a perfect matching. -/
def transposeMatching {n : Nat} (mu : Matching (Fin n) (Fin n)) :
    Matching (Fin n) (Fin n) where
  manPartner := mu.womanPartner
  womanPartner := mu.manPartner
  left_inv := mu.right_inv
  right_inv := mu.left_inv

@[simp] theorem transposeMatching_manPartner {n : Nat}
    (mu : Matching (Fin n) (Fin n)) (m : Fin n) :
    (transposeMatching mu).manPartner m = mu.womanPartner m := rfl

@[simp] theorem transposeMatching_womanPartner {n : Nat}
    (mu : Matching (Fin n) (Fin n)) (w : Fin n) :
    (transposeMatching mu).womanPartner w = mu.manPartner w := rfl

@[simp] theorem transposeMatching_transpose {n : Nat}
    (mu : Matching (Fin n) (Fin n)) :
    transposeMatching (transposeMatching mu) = mu := by
  cases mu
  rfl

theorem stable_transpose_iff {n : Nat} (P : Profile (Fin n) (Fin n))
    (mu : Matching (Fin n) (Fin n)) :
    Stable (transposeProfile P) (transposeMatching mu) ↔ Stable P mu := by
  constructor
  · intro h m w hblock
    exact h w m ⟨hblock.2, hblock.1⟩
  · intro h w m hblock
    exact h m w ⟨hblock.2, hblock.1⟩

/-- The genuine men-better join, converted back to the proof-field-free
matching code used by the entropy development. -/
def codedStableSup {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) : CodedStable P := by
  have hmu : Stable P.toCore mu.1.toCore :=
    (stableCode_iff_core P mu.1).1 mu.2
  have hsigma : Stable P.toCore sigma.1.toCore :=
    (stableCode_iff_core P sigma.1).1 sigma.2
  let j := stableMenJoin P.toCore mu.1.toCore sigma.1.toCore hmu hsigma
  refine ⟨MatchingCode.ofCore j, ?_⟩
  apply (stableCode_iff_core P (MatchingCode.ofCore j)).2
  simpa [j, MatchingCode.toCore, MatchingCode.ofCore] using
    (stableMenJoin_isStable P.toCore mu.1.toCore sigma.1.toCore hmu hsigma)

@[simp] theorem codedStableSup_apply {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) (m : Fin n) :
    (codedStableSup P mu sigma).1 m =
      if P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
      then mu.1 m else sigma.1 m := by
  rfl

/-- The genuine men-worse meet, obtained by taking the men-better join in
the transposed (women-as-men) instance and transposing back. -/
def codedStableInf {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) : CodedStable P := by
  have hmu : Stable P.toCore mu.1.toCore :=
    (stableCode_iff_core P mu.1).1 mu.2
  have hsigma : Stable P.toCore sigma.1.toCore :=
    (stableCode_iff_core P sigma.1).1 sigma.2
  have htmu : Stable (transposeProfile P.toCore) (transposeMatching mu.1.toCore) :=
    (stable_transpose_iff P.toCore mu.1.toCore).2 hmu
  have htsigma : Stable (transposeProfile P.toCore) (transposeMatching sigma.1.toCore) :=
    (stable_transpose_iff P.toCore sigma.1.toCore).2 hsigma
  let tj := stableMenJoin (transposeProfile P.toCore)
    (transposeMatching mu.1.toCore) (transposeMatching sigma.1.toCore)
    htmu htsigma
  let meetCore := transposeMatching tj
  have hmeet : Stable P.toCore meetCore := by
    apply (stable_transpose_iff P.toCore meetCore).1
    simpa [meetCore, tj] using
      (stableMenJoin_isStable (transposeProfile P.toCore)
        (transposeMatching mu.1.toCore) (transposeMatching sigma.1.toCore)
        htmu htsigma)
  refine ⟨MatchingCode.ofCore meetCore, ?_⟩
  apply (stableCode_iff_core P (MatchingCode.ofCore meetCore)).2
  simpa [MatchingCode.toCore, MatchingCode.ofCore] using hmeet

@[simp] theorem codedStableInf_apply {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) (m : Fin n) :
    (codedStableInf P mu sigma).1 m =
      if P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
      then sigma.1 m else mu.1 m := by
  simp [codedStableInf, transposeMatching, transposeProfile,
    ProfileCode.toCore, MatchingCode.toCore, MatchingCode.ofCore]

instance codedStablePartialOrder {n : Nat} (P : ProfileCode n) :
    PartialOrder (CodedStable P) where
  le mu sigma := ∀ m, P.manRank m (sigma.1 m) ≤ P.manRank m (mu.1 m)
  le_refl mu m := le_rfl
  le_trans mu sigma tau hms hst m := (hst m).trans (hms m)
  le_antisymm mu sigma hms hsm := by
    apply Subtype.ext
    apply Equiv.ext
    intro m
    apply (P.manRank m).injective
    exact le_antisymm (hsm m) (hms m)

theorem codedStable_le_iff {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) :
    mu ≤ sigma ↔ ∀ m, P.manRank m (sigma.1 m) ≤ P.manRank m (mu.1 m) :=
  Iff.rfl

instance codedStableLattice {n : Nat} (P : ProfileCode n) :
    Lattice (CodedStable P) where
  sup := codedStableSup P
  le_sup_left := by
    intro mu sigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simp [codedStableSup_apply, h]
    · simp [codedStableSup_apply, h, le_of_not_gt h]
  le_sup_right := by
    intro mu sigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simp [codedStableSup_apply, h, h.le]
    · simp [codedStableSup_apply, h]
  sup_le := by
    intro mu sigma tau hmu hsigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simpa [codedStableSup_apply, h] using hmu m
    · simpa [codedStableSup_apply, h] using hsigma m
  inf := codedStableInf P
  inf_le_left := by
    intro mu sigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simp [codedStableInf_apply, h, h.le]
    · simp [codedStableInf_apply, h]
  inf_le_right := by
    intro mu sigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simp [codedStableInf_apply, h]
    · simp [codedStableInf_apply, h, le_of_not_gt h]
  le_inf := by
    intro tau mu sigma hmu hsigma m
    by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
    · simpa [codedStableInf_apply, h] using hsigma m
    · simpa [codedStableInf_apply, h] using hmu m

@[simp] theorem manRank_sup {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) (m : Fin n) :
    P.manRank m ((mu ⊔ sigma).1 m) =
      min (P.manRank m (mu.1 m)) (P.manRank m (sigma.1 m)) := by
  change P.manRank m ((codedStableSup P mu sigma).1 m) = _
  rw [codedStableSup_apply]
  by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
  · simp [h, h.le]
  · have hle : P.manRank m (sigma.1 m) ≤ P.manRank m (mu.1 m) :=
      le_of_not_gt h
    simp [h, hle]

@[simp] theorem manRank_inf {n : Nat} (P : ProfileCode n)
    (mu sigma : CodedStable P) (m : Fin n) :
    P.manRank m ((mu ⊓ sigma).1 m) =
      max (P.manRank m (mu.1 m)) (P.manRank m (sigma.1 m)) := by
  change P.manRank m ((codedStableInf P mu sigma).1 m) = _
  rw [codedStableInf_apply]
  by_cases h : P.manRank m (mu.1 m) < P.manRank m (sigma.1 m)
  · simp [h, h.le]
  · have hle : P.manRank m (sigma.1 m) ≤ P.manRank m (mu.1 m) :=
      le_of_not_gt h
    simp [h, hle]

instance codedStableDistribLattice {n : Nat} (P : ProfileCode n) :
    DistribLattice (CodedStable P) where
  le_sup_inf := by
    intro mu sigma tau m
    simp only [manRank_sup, manRank_inf]
    simp [min_def, max_def]
    split_ifs <;> omega

/-- Mathlib's Birkhoff representation now applies directly to the genuine
finite stable-matching lattice of every coded profile. -/
noncomputable def stableBirkhoffLowerSet {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) :
    CodedStable P ≃o LowerSet {mu : CodedStable P // SupIrred mu} :=
  by
    classical
    let mu := Classical.choose hstable
    have hmu : mu ∈ stableSet P := Classical.choose_spec hstable
    letI : Nonempty (CodedStable P) :=
      ⟨⟨mu, (mem_stableSet_iff P mu).1 hmu⟩⟩
    letI : OrderBot (CodedStable P) := Fintype.toOrderBot _
    exact OrderIso.lowerSetSupIrred

abbrev CanonicalRotation {n : Nat} (P : ProfileCode n) :=
  {mu : CodedStable P // SupIrred mu}

theorem stableCount_eq_fintype_card_codedStable {n : Nat}
    (P : ProfileCode n) :
    stableCount P = Fintype.card (CodedStable P) := by
  unfold stableCount stableSet CodedStable
  simpa using (Fintype.card_subtype (fun mu : MatchingCode n ↦ Stable P mu)).symm

theorem stableCount_eq_card_birkhoffLowerSet {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty) :
    stableCount P = Nat.card (LowerSet (CanonicalRotation P)) := by
  classical
  letI : Fintype (LowerSet (CanonicalRotation P)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  rw [stableCount_eq_fintype_card_codedStable]
  exact Fintype.card_congr (stableBirkhoffLowerSet P hstable).toEquiv

/-- The canonical finite rotation ideal attached to an actual stable
matching by the Birkhoff order isomorphism. -/
noncomputable def stableRotationIdeal {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (mu : CodedStable P) :
    Finset (CanonicalRotation P) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  exact (((stableBirkhoffLowerSet P hstable) mu : LowerSet (CanonicalRotation P)) :
    Set (CanonicalRotation P)).toFinset

theorem stableRotationIdeal_isIdeal {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (mu : CodedStable P) :
    IsFinsetIdeal (stableRotationIdeal P hstable mu) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  intro r s hrs hs
  rw [stableRotationIdeal, Set.mem_toFinset] at hs ⊢
  exact ((stableBirkhoffLowerSet P hstable) mu).lower hrs hs

theorem mem_stableRotationIdeal_iff {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (mu : CodedStable P)
    (r : CanonicalRotation P) :
    r ∈ stableRotationIdeal P hstable mu ↔ r.1 ≤ mu := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  simp only [stableRotationIdeal, Set.mem_toFinset]
  change r.1 ≤ mu ↔ r.1 ≤ mu
  rfl

theorem stableRotationIdeal_injective {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) :
    Function.Injective (stableRotationIdeal P hstable) := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  intro mu sigma h
  apply (stableBirkhoffLowerSet P hstable).injective
  ext r
  have hr := Finset.ext_iff.mp h r
  simpa [stableRotationIdeal] using hr

/-- Convert an arbitrary finite downset of canonical rotations back to the
genuine stable matching supplied by Birkhoff's order isomorphism. -/
def lowerSetOfFinsetIdeal {R : Type*} [PartialOrder R] [DecidableEq R]
    (D : Finset R) (hD : IsFinsetIdeal D) : LowerSet R where
  carrier := {r | r ∈ D}
  lower' := by
    intro r s hrs hs
    exact hD hrs hs

noncomputable def codedStableOfIdeal {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty)
    (D : Finset (CanonicalRotation P)) (hD : IsFinsetIdeal D) :
    CodedStable P :=
  (stableBirkhoffLowerSet P hstable).symm (lowerSetOfFinsetIdeal D hD)

@[simp] theorem stableRotationIdeal_codedStableOfIdeal_eq {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (D : Finset (CanonicalRotation P)) (hD : IsFinsetIdeal D) :
    stableRotationIdeal P hstable
      (codedStableOfIdeal P hstable D hD) = D := by
  classical
  letI : Fintype (CanonicalRotation P) := Fintype.ofFinite _
  ext r
  simp [stableRotationIdeal, codedStableOfIdeal, lowerSetOfFinsetIdeal]

/-- Thus the profile-level ideal map is not merely injective: every finite
canonical downset, including every deletion image used later, is realized by
an actual stable matching of the original profile. -/
theorem stableRotationIdeal_surjective_onto_ideals {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (D : Finset (CanonicalRotation P)) (hD : IsFinsetIdeal D) :
    ∃ mu : CodedStable P, stableRotationIdeal P hstable mu = D := by
  exact ⟨codedStableOfIdeal P hstable D hD,
    stableRotationIdeal_codedStableOfIdeal_eq P hstable D hD⟩

end

end StableMatchingsJointCharging
