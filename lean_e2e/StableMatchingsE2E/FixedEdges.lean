import StableMatchingsE2E.ProfileCode

/-!
# Fixed-edge fibers

This file formalizes the deletion injection used for fixed-edge
completions.  A compatible prescription is represented by a stable base
matching and a set of men whose partners are fixed to their base values.
Deleting those couples sends every stable completion injectively into the
stable matchings of the restricted instance.  Surjectivity is neither true
in general nor needed.
-/

namespace StableMatchingsE2E

open StableMatchings355

/-- Two matching codes agree on every man in `A`. -/
def AgreesOn {n : Nat} (A : Finset (Fin n))
    (base mu : MatchingCode n) : Prop :=
  ∀ m, m ∈ A → mu m = base m

instance {n : Nat} (A : Finset (Fin n)) (base mu : MatchingCode n) :
    Decidable (AgreesOn A base mu) := by
  unfold AgreesOn
  infer_instance

/-- Stable matchings extending the prescription supplied by `base` on `A`. -/
def fixedFiber {n : Nat} (P : ProfileCode n) (base : MatchingCode n)
    (A : Finset (Fin n)) : Finset (MatchingCode n) :=
  (stableSet P).filter (AgreesOn A base)

theorem mem_fixedFiber_iff {n : Nat} (P : ProfileCode n)
    (base mu : MatchingCode n) (A : Finset (Fin n)) :
    mu ∈ fixedFiber P base A ↔ Stable P mu ∧ AgreesOn A base mu := by
  simp [fixedFiber, mem_stableSet_iff]

/-- A matching extends an explicitly given prescription on `A`. -/
def ExtendsPrescription {n : Nat} (A : Finset (Fin n))
    (eta : ↥A → Fin n) (mu : MatchingCode n) : Prop :=
  ∀ m, mu m.1 = eta m

instance {n : Nat} (A : Finset (Fin n)) (eta : ↥A → Fin n)
    (mu : MatchingCode n) : Decidable (ExtendsPrescription A eta mu) := by
  unfold ExtendsPrescription
  infer_instance

/-- Stable completions of an explicit fixed-edge prescription. -/
def prescribedFiber {n : Nat} (P : ProfileCode n) (A : Finset (Fin n))
    (eta : ↥A → Fin n) : Finset (MatchingCode n) :=
  (stableSet P).filter (ExtendsPrescription A eta)

theorem mem_prescribedFiber_iff {n : Nat} (P : ProfileCode n)
    (A : Finset (Fin n)) (eta : ↥A → Fin n) (mu : MatchingCode n) :
    mu ∈ prescribedFiber P A eta ↔
      Stable P mu ∧ ExtendsPrescription A eta mu := by
  simp [prescribedFiber, mem_stableSet_iff]

/-- Once a compatible extension `base` is chosen, the explicit prescription
fiber is exactly the fiber agreeing with `base` on `A`. -/
theorem prescribedFiber_eq_fixedFiber_of_extends {n : Nat}
    (P : ProfileCode n) (A : Finset (Fin n)) (eta : ↥A → Fin n)
    (base : MatchingCode n) (hbaseExt : ExtendsPrescription A eta base) :
    prescribedFiber P A eta = fixedFiber P base A := by
  ext mu
  rw [mem_prescribedFiber_iff, mem_fixedFiber_iff]
  constructor
  · rintro ⟨hstable, hmuExt⟩
    refine ⟨hstable, ?_⟩
    intro m hm
    let ms : ↥A := ⟨m, hm⟩
    calc
      mu m = eta ms := hmuExt ms
      _ = base m := (hbaseExt ms).symm
  · rintro ⟨hstable, hagree⟩
    refine ⟨hstable, ?_⟩
    intro ms
    calc
      mu ms.1 = base ms.1 := hagree ms.1 ms.2
      _ = eta ms := hbaseExt ms

/-- Men not covered by the prescription. -/
abbrev FreeMan {n : Nat} (A : Finset (Fin n)) :=
  {m : Fin n // m ∉ A}

/-- Women not paired by `base` to a prescribed man. -/
abbrev FreeWoman {n : Nat} (base : MatchingCode n)
    (A : Finset (Fin n)) :=
  {w : Fin n // base.symm w ∉ A}

/-- The base matching identifies the two free sides. -/
def baseFreeEquiv {n : Nat} (base : MatchingCode n)
    (A : Finset (Fin n)) : FreeMan A ≃ FreeWoman base A where
  toFun m := ⟨base m.1, by simpa using m.2⟩
  invFun w := ⟨base.symm w.1, w.2⟩
  left_inv m := by
    apply Subtype.ext
    exact base.symm_apply_apply m.1
  right_inv w := by
    apply Subtype.ext
    exact base.apply_symm_apply w.1

/-- Number of unfixed men. -/
def freeSize {n : Nat} (A : Finset (Fin n)) : Nat :=
  Fintype.card (FreeMan A)

theorem freeSize_eq {n : Nat} (A : Finset (Fin n)) :
    freeSize A = n - A.card := by
  simpa [freeSize] using
    (Fintype.card_subtype_compl (fun m : Fin n ↦ m ∈ A))

noncomputable def freeManEquivFin {n : Nat} (A : Finset (Fin n)) :
    FreeMan A ≃ Fin (freeSize A) :=
  Fintype.equivFin (FreeMan A)

noncomputable def freeWomanEquivFin {n : Nat} (base : MatchingCode n)
    (A : Finset (Fin n)) : FreeWoman base A ≃ Fin (freeSize A) :=
  (baseFreeEquiv base A).symm.trans (freeManEquivFin A)

/-- Restrict the original strict preferences to the free participants. -/
def freeProfileCore {n : Nat} (P : ProfileCode n) (base : MatchingCode n)
    (A : Finset (Fin n)) : Profile (FreeMan A) (FreeWoman base A) where
  manPref m a b := P.toCore.manPref m.1 a.1 b.1
  womanPref w a b := P.toCore.womanPref w.1 a.1 b.1
  man_decidable := fun m a b ↦ P.toCore.man_decidable m.1 a.1 b.1
  woman_decidable := fun w a b ↦ P.toCore.woman_decidable w.1 a.1 b.1
  man_asymm := fun m a b ↦ P.toCore.man_asymm m.1 a.1 b.1
  woman_asymm := fun w a b ↦ P.toCore.woman_asymm w.1 a.1 b.1
  man_trans := fun m a b c ↦ P.toCore.man_trans m.1 a.1 b.1 c.1
  woman_trans := fun w a b c ↦ P.toCore.woman_trans w.1 a.1 b.1 c.1
  man_total := by
    intro m a b hab
    exact P.toCore.man_total m.1 a.1 b.1
      (fun h ↦ hab (Subtype.ext h))
  woman_total := by
    intro w a b hab
    exact P.toCore.woman_total w.1 a.1 b.1
      (fun h ↦ hab (Subtype.ext h))

/-- Relabel both sides of a relation-based profile by equivalences. -/
def relabelProfile {M W M' W' : Type} (Q : Profile M W)
    (em : M ≃ M') (ew : W ≃ W') : Profile M' W' where
  manPref m a b := Q.manPref (em.symm m) (ew.symm a) (ew.symm b)
  womanPref w a b := Q.womanPref (ew.symm w) (em.symm a) (em.symm b)
  man_decidable := fun m a b ↦
    Q.man_decidable (em.symm m) (ew.symm a) (ew.symm b)
  woman_decidable := fun w a b ↦
    Q.woman_decidable (ew.symm w) (em.symm a) (em.symm b)
  man_asymm := fun m a b ↦ Q.man_asymm (em.symm m) (ew.symm a) (ew.symm b)
  woman_asymm := fun w a b ↦ Q.woman_asymm (ew.symm w) (em.symm a) (em.symm b)
  man_trans := fun m a b c ↦
    Q.man_trans (em.symm m) (ew.symm a) (ew.symm b) (ew.symm c)
  woman_trans := fun w a b c ↦
    Q.woman_trans (ew.symm w) (em.symm a) (em.symm b) (em.symm c)
  man_total := by
    intro m a b hab
    exact Q.man_total (em.symm m) (ew.symm a) (ew.symm b)
      (ew.symm.injective.ne hab)
  woman_total := by
    intro w a b hab
    exact Q.woman_total (ew.symm w) (em.symm a) (em.symm b)
      (em.symm.injective.ne hab)

/-- Relabel a perfect matching by the same pair of equivalences. -/
def relabelMatching {M W M' W' : Type} (mu : Matching M W)
    (em : M ≃ M') (ew : W ≃ W') : Matching M' W' where
  manPartner m := ew (mu.manPartner (em.symm m))
  womanPartner w := em (mu.womanPartner (ew.symm w))
  left_inv m := by simp [mu.left_inv]
  right_inv w := by simp [mu.right_inv]

theorem relabelMatching_stable {M W M' W' : Type} (Q : Profile M W)
    (mu : Matching M W) (em : M ≃ M') (ew : W ≃ W')
    (hmu : StableMatchings355.Stable Q mu) :
    StableMatchings355.Stable (relabelProfile Q em ew)
      (relabelMatching mu em ew) := by
  intro m w hblocks
  apply hmu (em.symm m) (ew.symm w)
  simpa [StableMatchings355.Blocks, relabelProfile, relabelMatching] using hblocks

/-- Restrict a matching agreeing with `base` on `A` to the free sides. -/
def freeMatchingCore {n : Nat} (base mu : MatchingCode n)
    (A : Finset (Fin n)) (hagree : AgreesOn A base mu) :
    Matching (FreeMan A) (FreeWoman base A) where
  manPartner m := ⟨mu m.1, by
    intro hfixed
    apply m.2
    have heq : base.symm (mu m.1) = m.1 := by
      apply mu.injective
      calc
        mu (base.symm (mu m.1)) = base (base.symm (mu m.1)) :=
          hagree _ hfixed
        _ = mu m.1 := base.apply_symm_apply _
    exact heq ▸ hfixed⟩
  womanPartner w := ⟨mu.symm w.1, by
    intro hfixed
    apply w.2
    have heq : base.symm w.1 = mu.symm w.1 := by
      apply base.injective
      calc
        base (base.symm w.1) = w.1 := base.apply_symm_apply _
        _ = mu (mu.symm w.1) := (mu.apply_symm_apply _).symm
        _ = base (mu.symm w.1) := hagree _ hfixed
    exact heq ▸ hfixed⟩
  left_inv m := by
    apply Subtype.ext
    exact mu.symm_apply_apply m.1
  right_inv w := by
    apply Subtype.ext
    exact mu.apply_symm_apply w.1

theorem freeMatchingCore_stable {n : Nat} (P : ProfileCode n)
    (base mu : MatchingCode n) (A : Finset (Fin n))
    (hagree : AgreesOn A base mu) (hmu : Stable P mu) :
    StableMatchings355.Stable (freeProfileCore P base A)
      (freeMatchingCore base mu A hagree) := by
  have hcore : StableMatchings355.Stable P.toCore mu.toCore :=
    (stableCode_iff_core P mu).1 hmu
  intro m w hblocks
  apply hcore m.1 w.1
  simpa [StableMatchings355.Blocks, freeProfileCore,
    freeMatchingCore, MatchingCode.toCore] using hblocks

/-- The restricted instance, relabeled onto `Fin (n-|A|)`. -/
noncomputable def freeProfileCode {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (A : Finset (Fin n)) : ProfileCode (freeSize A) :=
  ProfileCode.ofCore
    (relabelProfile (freeProfileCore P base A)
      (freeManEquivFin A) (freeWomanEquivFin base A))

noncomputable def freeMatchingCode {n : Nat} (base mu : MatchingCode n)
    (A : Finset (Fin n)) (hagree : AgreesOn A base mu) :
    MatchingCode (freeSize A) :=
  MatchingCode.ofCore
    (relabelMatching (freeMatchingCore base mu A hagree)
      (freeManEquivFin A) (freeWomanEquivFin base A))

theorem freeMatchingCode_stable {n : Nat} (P : ProfileCode n)
    (base mu : MatchingCode n) (A : Finset (Fin n))
    (hagree : AgreesOn A base mu) (hmu : Stable P mu) :
    Stable (freeProfileCode P base A)
      (freeMatchingCode base mu A hagree) := by
  apply (stable_full_ofCore_iff
    (relabelProfile (freeProfileCore P base A)
      (freeManEquivFin A) (freeWomanEquivFin base A))
    (relabelMatching (freeMatchingCore base mu A hagree)
      (freeManEquivFin A) (freeWomanEquivFin base A))).2
  apply relabelMatching_stable
  exact freeMatchingCore_stable P base mu A hagree hmu

/-- Deletion of the fixed couples is injective on the stable fiber. -/
noncomputable def fixedFiberEmbedding {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (A : Finset (Fin n)) :
    ↥(fixedFiber P base A) ↪ ↥(stableSet (freeProfileCode P base A)) where
  toFun x := by
    have hx := (mem_fixedFiber_iff P base x.1 A).1 x.2
    exact ⟨freeMatchingCode base x.1 A hx.2,
      (mem_stableSet_iff _ _).2
        (freeMatchingCode_stable P base x.1 A hx.2 hx.1)⟩
  inj' := by
    intro x y hxy
    have hx := (mem_fixedFiber_iff P base x.1 A).1 x.2
    have hy := (mem_fixedFiber_iff P base y.1 A).1 y.2
    apply Subtype.ext
    apply Equiv.ext
    intro m
    by_cases hm : m ∈ A
    · exact (hx.2 m hm).trans (hy.2 m hm).symm
    · let mf : FreeMan A := ⟨m, hm⟩
      have hcodes : freeMatchingCode base x.1 A hx.2 =
          freeMatchingCode base y.1 A hy.2 :=
        congrArg Subtype.val hxy
      have happ := congrArg (fun nu : MatchingCode (freeSize A) ↦
        nu (freeManEquivFin A mf)) hcodes
      simp only [freeMatchingCode, MatchingCode.ofCore_apply,
        relabelMatching, Equiv.symm_apply_apply] at happ
      have hfree :
          (⟨x.1 m, by
            exact (freeMatchingCore base x.1 A hx.2).manPartner mf |>.2⟩ :
              FreeWoman base A) =
          ⟨y.1 m, by
            exact (freeMatchingCore base y.1 A hy.2).manPartner mf |>.2⟩ := by
        apply (freeWomanEquivFin base A).injective
        exact happ
      exact congrArg Subtype.val hfree

/-- A fixed-edge fiber has at most as many completions as an unrestricted
instance on the unfixed participants. -/
theorem fixedFiber_card_le_SM {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (A : Finset (Fin n)) :
    (fixedFiber P base A).card ≤ SM (n - A.card) := by
  have hinj : Fintype.card ↥(fixedFiber P base A) ≤
      Fintype.card ↥(stableSet (freeProfileCode P base A)) :=
    Fintype.card_le_of_injective (fixedFiberEmbedding P base A)
      (fixedFiberEmbedding P base A).injective
  calc
    (fixedFiber P base A).card = Fintype.card ↥(fixedFiber P base A) := by
      simp
    _ ≤ Fintype.card ↥(stableSet (freeProfileCode P base A)) := hinj
    _ = stableCount (freeProfileCode P base A) := by simp [stableCount]
    _ ≤ SM (freeSize A) := SM_spec _
    _ = SM (n - A.card) := by rw [freeSize_eq]

/-- Fixing all men to a compatible stable matching leaves exactly that
matching. -/
theorem fixedFiber_eq_singleton_of_card_eq {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (A : Finset (Fin n))
    (hbase : Stable P base) (hcard : A.card = n) :
    fixedFiber P base A = {base} := by
  have hA : A = Finset.univ :=
    Finset.eq_univ_of_card A (by simpa using hcard)
  subst A
  ext mu
  rw [Finset.mem_singleton]
  constructor
  · intro hmu
    have hagree := (mem_fixedFiber_iff P base mu Finset.univ).1 hmu |>.2
    apply Equiv.ext
    intro m
    exact hagree m (Finset.mem_univ m)
  · intro hmu
    subst mu
    exact (mem_fixedFiber_iff P base base Finset.univ).2
      ⟨hbase, fun _ _ ↦ rfl⟩

theorem fixedFiber_card_eq_one_of_card_eq {n : Nat} (P : ProfileCode n)
    (base : MatchingCode n) (A : Finset (Fin n))
    (hbase : Stable P base) (hcard : A.card = n) :
    (fixedFiber P base A).card = 1 := by
  rw [fixedFiber_eq_singleton_of_card_eq P base A hbase hcard]
  simp

/-- Structural bound stated directly for a compatible explicit
prescription. -/
theorem prescribedFiber_card_le_SM {n : Nat} (P : ProfileCode n)
    (A : Finset (Fin n)) (eta : ↥A → Fin n) (base : MatchingCode n)
    (hbaseExt : ExtendsPrescription A eta base) :
    (prescribedFiber P A eta).card ≤ SM (n - A.card) := by
  rw [prescribedFiber_eq_fixedFiber_of_extends P A eta base hbaseExt]
  exact fixedFiber_card_le_SM P base A

theorem prescribedFiber_card_eq_one_of_card_eq {n : Nat}
    (P : ProfileCode n) (A : Finset (Fin n)) (eta : ↥A → Fin n)
    (base : MatchingCode n) (hbase : Stable P base)
    (hbaseExt : ExtendsPrescription A eta base) (hcard : A.card = n) :
    (prescribedFiber P A eta).card = 1 := by
  rw [prescribedFiber_eq_fixedFiber_of_extends P A eta base hbaseExt]
  exact fixedFiber_card_eq_one_of_card_eq P base A hbase hcard

end StableMatchingsE2E
