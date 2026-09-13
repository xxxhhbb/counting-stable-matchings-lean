import StableMatchings355.Core

namespace StableMatchings355

/-! A self-contained finite proof of the exact `HasMenJoin` interface consumed
by `stablePair_sidedness`.  No stable-lattice theorem is assumed. -/

private theorem length_le_of_nodup_subset {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} (hnd : xs.Nodup) (hsub : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnd
      have ha : a ∈ ys := hsub (by simp)
      have htail : xs ⊆ ys.erase a := by
        intro b hb
        have hba : b ≠ a := by
          intro e
          apply hnd.1
          simpa [e] using hb
        exact (List.mem_erase_of_ne hba).2 (hsub (by simp [hb]))
      have hle := ih hnd.2 htail
      rw [List.length_erase_of_mem ha] at hle
      have hy : 0 < ys.length := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

private theorem nodup_ofFn_of_injective {α : Type} {n : Nat} (f : Fin n -> α)
    (hf : Function.Injective f) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have heq : i.succ = (0 : Fin (n + 1)) := hf hi
        have hval := congrArg Fin.val heq
        simp at hval
      · apply ih (fun i => f i.succ)
        intro i j hij
        apply Fin.eq_of_val_eq
        have hval := congrArg Fin.val (hf hij)
        simpa using hval

private theorem fin_inj_surj {n : Nat} (f : Fin n -> Fin n)
    (hf : Function.Injective f) : Function.Surjective f := by
  intro y
  have hy : y ∈ List.finRange n := List.mem_finRange y
  apply Classical.byContradiction
  intro hnone
  have hnotmem : y ∉ List.ofFn f := by
    intro hm
    rw [List.mem_ofFn] at hm
    obtain ⟨i, hi⟩ := hm
    exact hnone ⟨i, hi⟩
  have hsub : List.ofFn f ⊆ (List.finRange n).erase y := by
    intro z hz
    have hzne : z ≠ y := by
      intro e
      apply hnotmem
      simpa [e] using hz
    exact (List.mem_erase_of_ne hzne).2 (List.mem_finRange z)
  have hle := length_le_of_nodup_subset (nodup_ofFn_of_injective f hf) hsub
  rw [List.length_ofFn, List.length_erase_of_mem hy, List.length_finRange] at hle
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le y.val) y.isLt
  omega

private def finiteMenChoice {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m : Fin n) : Fin n :=
  @ite (Fin n) (P.manPref m (mu.manPartner m) (sigma.manPartner m))
    (P.man_decidable m _ _) (mu.manPartner m) (sigma.manPartner m)

private theorem menChoice_eq_mu_of_pref {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m)
    (h : P.manPref m (mu.manPartner m) (sigma.manPartner m)) :
    finiteMenChoice P mu sigma m = mu.manPartner m := by
  simp [finiteMenChoice, h]

private theorem menChoice_eq_sigma_of_pref {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m)
    (h : P.manPref m (sigma.manPartner m) (mu.manPartner m)) :
    finiteMenChoice P mu sigma m = sigma.manPartner m := by
  have hn := P.man_asymm m _ _ h
  simp [finiteMenChoice, hn]

private theorem menChoice_old_partner {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m) :
    finiteMenChoice P mu sigma m = mu.manPartner m \/
    finiteMenChoice P mu sigma m = sigma.manPartner m := by
  unfold finiteMenChoice
  split <;> simp_all

private theorem cross_mu_sigma_impossible {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) {a b w : Fin n}
    (hab : a ≠ b) (ha : finiteMenChoice P mu sigma a = w)
    (hb : finiteMenChoice P mu sigma b = w)
    (hmuA : mu.manPartner a = w) (hsigmaB : sigma.manPartner b = w) : False := by
  have hsigmaA_ne : sigma.manPartner a ≠ w := by
    intro h
    apply hab
    apply Matching.manPartner_injective sigma
    exact h.trans hsigmaB.symm
  have hmuB_ne : mu.manPartner b ≠ w := by
    intro h
    apply hab
    symm
    apply Matching.manPartner_injective mu
    exact h.trans hmuA.symm
  have hpa : P.manPref a (mu.manPartner a) (sigma.manPartner a) := by
    apply Classical.byContradiction
    intro hn
    have hc : finiteMenChoice P mu sigma a = sigma.manPartner a := by
      simp [finiteMenChoice, hn]
    exact hsigmaA_ne (hc.symm.trans ha)
  have hpb : P.manPref b (sigma.manPartner b) (mu.manPartner b) := by
    have hd : sigma.manPartner b ≠ mu.manPartner b := by
      intro h
      exact hmuB_ne (h.symm.trans hsigmaB)
    rcases P.man_total b (sigma.manPartner b) (mu.manPartner b) hd with hp | hp
    · exact hp
    · have hc : finiteMenChoice P mu sigma b = mu.manPartner b := by
        simp [finiteMenChoice, hp]
      exact False.elim (hmuB_ne (hc.symm.trans hb))
  have hwa_not : Not (P.womanPref w a b) := by
    intro hw
    have hsigW : sigma.womanPartner w = b := by
      rw [← hsigmaB]
      exact sigma.left_inv b
    apply hsigma a w
    exact ⟨by simpa [hmuA] using hpa, by simpa [hsigW] using hw⟩
  have hwb_not : Not (P.womanPref w b a) := by
    intro hw
    have hmuW : mu.womanPartner w = a := by
      rw [← hmuA]
      exact mu.left_inv a
    apply hmu b w
    exact ⟨by simpa [hsigmaB] using hpb, by simpa [hmuW] using hw⟩
  rcases P.woman_total w a b hab with hw | hw
  · exact hwa_not hw
  · exact hwb_not hw

private theorem finiteMenChoice_injective {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) :
    Function.Injective (finiteMenChoice P mu sigma) := by
  intro a b habChoice
  apply Classical.byContradiction
  intro hab
  have hne : a ≠ b := hab
  rcases menChoice_old_partner P mu sigma a with haMu | haSigma <;>
    rcases menChoice_old_partner P mu sigma b with hbMu | hbSigma
  · exact hne (Matching.manPartner_injective mu (haMu.symm.trans (habChoice.trans hbMu)))
  · have hcommon : mu.manPartner a = sigma.manPartner b :=
      haMu.symm.trans (habChoice.trans hbSigma)
    exact cross_mu_sigma_impossible P mu sigma hmu hsigma hne
      haMu (hbSigma.trans hcommon.symm) rfl hcommon.symm
  · have hcommon : mu.manPartner b = sigma.manPartner a :=
      hbMu.symm.trans (habChoice.symm.trans haSigma)
    exact cross_mu_sigma_impossible P mu sigma hmu hsigma hne.symm
      hbMu (haSigma.trans hcommon.symm) rfl hcommon.symm
  · exact hne (Matching.manPartner_injective sigma (haSigma.symm.trans (habChoice.trans hbSigma)))

private noncomputable def finiteJoinWomanPartner {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) (w : Fin n) : Fin n :=
  Classical.choose (fin_inj_surj (finiteMenChoice P mu sigma)
    (finiteMenChoice_injective P mu sigma hmu hsigma) w)

private theorem finiteJoinWomanPartner_spec {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) (w : Fin n) :
    finiteMenChoice P mu sigma (finiteJoinWomanPartner P mu sigma hmu hsigma w) = w :=
  Classical.choose_spec (fin_inj_surj (finiteMenChoice P mu sigma)
    (finiteMenChoice_injective P mu sigma hmu hsigma) w)

private noncomputable def finiteMenJoin {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) : Matching (Fin n) (Fin n) where
  manPartner := finiteMenChoice P mu sigma
  womanPartner := finiteJoinWomanPartner P mu sigma hmu hsigma
  left_inv := by
    intro m
    apply finiteMenChoice_injective P mu sigma hmu hsigma
    exact finiteJoinWomanPartner_spec P mu sigma hmu hsigma (finiteMenChoice P mu sigma m)
  right_inv := finiteJoinWomanPartner_spec P mu sigma hmu hsigma

private theorem finite_join_preimage_old_partner {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (hmu : Stable P mu) (hsigma : Stable P sigma)
    (w : Fin n) :
    (finiteMenJoin P mu sigma hmu hsigma).womanPartner w = mu.womanPartner w \/
    (finiteMenJoin P mu sigma hmu hsigma).womanPartner w = sigma.womanPartner w := by
  let m := (finiteMenJoin P mu sigma hmu hsigma).womanPartner w
  have hm : (finiteMenJoin P mu sigma hmu hsigma).manPartner m = w :=
    (finiteMenJoin P mu sigma hmu hsigma).right_inv w
  change finiteMenChoice P mu sigma m = w at hm
  rcases menChoice_old_partner P mu sigma m with hOld | hOld
  · left
    apply Matching.manPartner_injective mu
    calc
      mu.manPartner m = w := hOld.symm.trans hm
      _ = mu.manPartner (mu.womanPartner w) := (mu.right_inv w).symm
  · right
    apply Matching.manPartner_injective sigma
    calc
      sigma.manPartner m = w := hOld.symm.trans hm
      _ = sigma.manPartner (sigma.womanPartner w) := (sigma.right_inv w).symm

private theorem man_pref_or_eq_of_join_eq_mu {n}
    (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m : Fin n)
    (h : finiteMenChoice P mu sigma m = mu.manPartner m) :
    Or (P.manPref m (mu.manPartner m) (sigma.manPartner m))
      (mu.manPartner m = sigma.manPartner m) := by
  by_cases hp : P.manPref m (mu.manPartner m) (sigma.manPartner m)
  · exact Or.inl hp
  · right
    simpa [finiteMenChoice, hp] using h.symm

private theorem man_pref_or_eq_of_join_eq_sigma {n}
    (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (m : Fin n)
    (h : finiteMenChoice P mu sigma m = sigma.manPartner m) :
    Or (P.manPref m (sigma.manPartner m) (mu.manPartner m))
      (sigma.manPartner m = mu.manPartner m) := by
  by_cases heq : sigma.manPartner m = mu.manPartner m
  · exact Or.inr heq
  · left
    have hnot : ¬ P.manPref m (mu.manPartner m) (sigma.manPartner m) := by
      intro hp
      have hjmu := menChoice_eq_mu_of_pref P mu sigma m hp
      exact heq (h.symm.trans hjmu)
    rcases P.man_total m (sigma.manPartner m) (mu.manPartner m) heq with hp | hp
    · exact hp
    · exact False.elim (hnot hp)

/-- The pointwise men-better choice of two stable matchings is stable.  This
is the missing closure theorem needed to put the finite stable-matchings
universe into its genuine lattice, rather than merely using the join as an
auxiliary perfect matching. -/
theorem finiteMenJoin_stable {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) :
    Stable P (finiteMenJoin P mu sigma hmu hsigma) := by
  intro m w hblock
  have hmold := menChoice_old_partner P mu sigma m
  have hwold := finite_join_preimage_old_partner P mu sigma hmu hsigma w
  rcases hmold with hmMu | hmSigma <;> rcases hwold with hwMu | hwSigma
  · apply hmu m w
    exact ⟨by simpa [finiteMenJoin, hmMu] using hblock.1,
      by simpa [hwMu] using hblock.2⟩
  · have hchoice : finiteMenChoice P mu sigma m = mu.manPartner m := hmMu
    rcases man_pref_or_eq_of_join_eq_mu P mu sigma m hchoice with hp | heq
    · apply hsigma m w
      exact ⟨P.man_trans m w (mu.manPartner m) (sigma.manPartner m)
          (by simpa [finiteMenJoin, hmMu] using hblock.1) hp,
        by simpa [hwSigma] using hblock.2⟩
    · apply hsigma m w
      exact ⟨by simpa [finiteMenJoin, hmMu, heq] using hblock.1,
        by simpa [hwSigma] using hblock.2⟩
  · have hchoice : finiteMenChoice P mu sigma m = sigma.manPartner m := hmSigma
    rcases man_pref_or_eq_of_join_eq_sigma P mu sigma m hchoice with hp | heq
    · apply hmu m w
      exact ⟨P.man_trans m w (sigma.manPartner m) (mu.manPartner m)
          (by simpa [finiteMenJoin, hmSigma] using hblock.1) hp,
        by simpa [hwMu] using hblock.2⟩
    · apply hmu m w
      exact ⟨by simpa [finiteMenJoin, hmSigma, heq] using hblock.1,
        by simpa [hwMu] using hblock.2⟩
  · apply hsigma m w
    exact ⟨by simpa [finiteMenJoin, hmSigma] using hblock.1,
      by simpa [hwSigma] using hblock.2⟩

/-- Public wrapper for the stable men-side join.  Its partner formula is
pointwise: each man receives his preferred partner among the two inputs. -/
noncomputable def stableMenJoin {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) :
    Matching (Fin n) (Fin n) :=
  finiteMenJoin P mu sigma hmu hsigma

@[simp] theorem stableMenJoin_manPartner {n}
    (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) (m : Fin n) :
    (stableMenJoin P mu sigma hmu hsigma).manPartner m =
      @ite (Fin n) (P.manPref m (mu.manPartner m) (sigma.manPartner m))
        (P.man_decidable m _ _) (mu.manPartner m) (sigma.manPartner m) := by
  rfl

theorem stableMenJoin_isStable {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) :
    Stable P (stableMenJoin P mu sigma hmu hsigma) :=
  finiteMenJoin_stable P mu sigma hmu hsigma

private theorem finite_join_woman_sigma_of_pref_mu {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (hmu : Stable P mu) (hsigma : Stable P sigma)
    (w) (h : P.womanPref w (mu.womanPartner w) (sigma.womanPartner w)) :
    (finiteMenJoin P mu sigma hmu hsigma).womanPartner w = sigma.womanPartner w := by
  rcases finite_join_preimage_old_partner P mu sigma hmu hsigma w with hj | hj
  · have hmen : P.manPref (mu.womanPartner w) w
        (sigma.manPartner (mu.womanPartner w)) := by
      have hneq : sigma.manPartner (mu.womanPartner w) ≠ w := by
        intro hs
        have hp : sigma.womanPartner w = mu.womanPartner w := by
          calc
            sigma.womanPartner w = sigma.womanPartner
                (sigma.manPartner (mu.womanPartner w)) := by rw [hs]
            _ = mu.womanPartner w := sigma.left_inv _
        exact (P.woman_asymm w _ _ h) (by simpa [hp] using h)
      have hjoin := (finiteMenJoin P mu sigma hmu hsigma).right_inv w
      change finiteMenChoice P mu sigma
        ((finiteMenJoin P mu sigma hmu hsigma).womanPartner w) = w at hjoin
      have hc : finiteMenChoice P mu sigma (mu.womanPartner w) = w := by
        simpa [hj] using hjoin
      apply Classical.byContradiction
      intro hn
      have hmuw : mu.manPartner (mu.womanPartner w) = w := mu.right_inv w
      have he : sigma.manPartner (mu.womanPartner w) = w := by
        simpa [finiteMenChoice, hn, hmuw] using hc
      exact hneq he
    exact False.elim (hsigma (mu.womanPartner w) w ⟨hmen, h⟩)
  · exact hj

private theorem finite_join_woman_mu_of_pref_sigma {n} (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n)) (hmu : Stable P mu) (hsigma : Stable P sigma)
    (w) (h : P.womanPref w (sigma.womanPartner w) (mu.womanPartner w)) :
    (finiteMenJoin P mu sigma hmu hsigma).womanPartner w = mu.womanPartner w := by
  rcases finite_join_preimage_old_partner P mu sigma hmu hsigma w with hj | hj
  · exact hj
  · have hmen : P.manPref (sigma.womanPartner w) w
        (mu.manPartner (sigma.womanPartner w)) := by
      have hneq : mu.manPartner (sigma.womanPartner w) ≠ w := by
        intro hm
        have hp : mu.womanPartner w = sigma.womanPartner w := by
          calc
            mu.womanPartner w = mu.womanPartner
                (mu.manPartner (sigma.womanPartner w)) := by rw [hm]
            _ = sigma.womanPartner w := mu.left_inv _
        exact (P.woman_asymm w _ _ h) (by simpa [hp] using h)
      have hjoin := (finiteMenJoin P mu sigma hmu hsigma).right_inv w
      change finiteMenChoice P mu sigma
        ((finiteMenJoin P mu sigma hmu hsigma).womanPartner w) = w at hjoin
      have hc : finiteMenChoice P mu sigma (sigma.womanPartner w) = w := by
        simpa [hj] using hjoin
      rcases P.man_total (sigma.womanPartner w) w
          (mu.manPartner (sigma.womanPartner w)) (by simpa using hneq.symm) with hp | hp
      · exact hp
      · have he : finiteMenChoice P mu sigma (sigma.womanPartner w) =
            mu.manPartner (sigma.womanPartner w) := by
              have hsigw : sigma.manPartner (sigma.womanPartner w) = w := sigma.right_inv w
              simp [finiteMenChoice, hp, hsigw]
        exact False.elim (hneq (he.symm.trans hc))
    exact False.elim (hmu (sigma.womanPartner w) w ⟨hmen, h⟩)

@[simp] theorem stableMenJoin_womanPartner {n}
    (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma) (w : Fin n) :
    (stableMenJoin P mu sigma hmu hsigma).womanPartner w =
      @ite (Fin n) (P.womanPref w (mu.womanPartner w) (sigma.womanPartner w))
        (P.woman_decidable w _ _) (sigma.womanPartner w) (mu.womanPartner w) := by
  by_cases hp : P.womanPref w (mu.womanPartner w) (sigma.womanPartner w)
  · simp only [hp, ↓reduceIte, stableMenJoin]
    exact finite_join_woman_sigma_of_pref_mu P mu sigma hmu hsigma w hp
  · simp only [hp, ↓reduceIte, stableMenJoin]
    by_cases heq : mu.womanPartner w = sigma.womanPartner w
    · rcases finite_join_preimage_old_partner P mu sigma hmu hsigma w with hj | hj
      · exact hj
      · exact hj.trans heq.symm
    · have hrev : P.womanPref w (sigma.womanPartner w) (mu.womanPartner w) := by
        rcases P.woman_total w (mu.womanPartner w) (sigma.womanPartner w) heq with h | h
        · exact False.elim (hp h)
        · exact h
      exact finite_join_woman_mu_of_pref_sigma P mu sigma hmu hsigma w hrev

theorem finite_hasMenJoin (n : Nat) (P : Profile (Fin n) (Fin n)) : HasMenJoin P := by
  intro mu sigma hmu hsigma
  refine ⟨finiteMenJoin P mu sigma hmu hsigma, ?_, ?_⟩
  · intro m
    exact ⟨menChoice_eq_mu_of_pref P mu sigma m,
      menChoice_eq_sigma_of_pref P mu sigma m⟩
  · intro w
    exact ⟨finite_join_woman_sigma_of_pref_mu P mu sigma hmu hsigma w,
      finite_join_woman_mu_of_pref_sigma P mu sigma hmu hsigma w⟩

/- These corollaries expose that the finite downstream statements no longer
   require a caller-supplied `HasMenJoin` hypothesis. -/
theorem finite_stablePair_sidedness (n : Nat) (P : Profile (Fin n) (Fin n))
    (mu sigma : Matching (Fin n) (Fin n))
    (hmu : Stable P mu) (hsigma : Stable P sigma)
    {m w : Fin n} (hsigmaPair : sigma.manPartner m = w)
    (hmuNotPair : mu.manPartner m ≠ w) :
    (P.manPref m (mu.manPartner m) w /\
       P.womanPref w m (mu.womanPartner w)) \/
    (P.manPref m w (mu.manPartner m) /\
       P.womanPref w (mu.womanPartner w) m) := by
  exact stablePair_sidedness P (finite_hasMenJoin n P) mu sigma
    hmu hsigma hsigmaPair hmuNotPair

theorem finite_fixedPartner_sameSide (n : Nat) (P : Profile (Fin n) (Fin n))
    (sigma mu nu : Matching (Fin n) (Fin n))
    (hsigma : Stable P sigma) (hmu : Stable P mu) (hnu : Stable P nu)
    {m w : Fin n} (hsigmaPair : sigma.manPartner m = w)
    (hfixed : mu.womanPartner w = nu.womanPartner w)
    (hmuNot : mu.manPartner m ≠ w) (hnuNot : nu.manPartner m ≠ w) :
    (P.manPref m (mu.manPartner m) w <->
       P.manPref m (nu.manPartner m) w) := by
  exact fixedPartner_sameSide P (finite_hasMenJoin n P) sigma mu nu
    hsigma hmu hnu hsigmaPair hfixed hmuNot hnuNot

end StableMatchings355
