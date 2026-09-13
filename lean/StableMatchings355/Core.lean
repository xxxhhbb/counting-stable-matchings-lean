import Std

namespace StableMatchings355

/-! A dependency-free formal core for strict complete stable marriage. -/

structure Profile (M W : Type) where
  manPref : M -> W -> W -> Prop
  womanPref : W -> M -> M -> Prop
  man_decidable : forall m a b, Decidable (manPref m a b)
  woman_decidable : forall w a b, Decidable (womanPref w a b)
  man_asymm : forall m a b, manPref m a b -> Not (manPref m b a)
  woman_asymm : forall w a b, womanPref w a b -> Not (womanPref w b a)
  man_trans : forall m a b c, manPref m a b -> manPref m b c -> manPref m a c
  woman_trans : forall w a b c, womanPref w a b -> womanPref w b c -> womanPref w a c
  man_total : forall m a b, a ≠ b -> manPref m a b \/ manPref m b a
  woman_total : forall w a b, a ≠ b -> womanPref w a b \/ womanPref w b a

structure Matching (M W : Type) where
  manPartner : M -> W
  womanPartner : W -> M
  left_inv : forall m, womanPartner (manPartner m) = m
  right_inv : forall w, manPartner (womanPartner w) = w

namespace Matching

theorem manPartner_injective {M W} (mu : Matching M W) :
    Function.Injective mu.manPartner := by
  intro a b h
  have := congrArg mu.womanPartner h
  simpa [mu.left_inv] using this

theorem womanPartner_injective {M W} (mu : Matching M W) :
    Function.Injective mu.womanPartner := by
  intro a b h
  have := congrArg mu.manPartner h
  simpa [mu.right_inv] using this

end Matching

def Blocks {M W} (P : Profile M W) (mu : Matching M W) (m : M) (w : W) : Prop :=
  P.manPref m w (mu.manPartner m) /\
  P.womanPref w m (mu.womanPartner w)

def Stable {M W} (P : Profile M W) (mu : Matching M W) : Prop :=
  forall m w, Not (Blocks P mu m w)

def StablePair {M W} (P : Profile M W) (m : M) (w : W) : Prop :=
  Exists fun mu : Matching M W => Stable P mu /\ mu.manPartner m = w

/- The exact lattice fact consumed by the sidedness argument.  It says that
   two stable matchings possess a matching assigning every man his better old
   partner and every woman her worse old partner.  Stability of the resulting
   matching is not needed below. -/
def HasMenJoin {M W} (P : Profile M W) : Prop :=
  forall (mu sigma : Matching M W), Stable P mu -> Stable P sigma ->
    Exists fun lam : Matching M W =>
      (forall m,
        (P.manPref m (mu.manPartner m) (sigma.manPartner m) ->
          lam.manPartner m = mu.manPartner m) /\
        (P.manPref m (sigma.manPartner m) (mu.manPartner m) ->
          lam.manPartner m = sigma.manPartner m)) /\
      (forall w,
        (P.womanPref w (mu.womanPartner w) (sigma.womanPartner w) ->
          lam.womanPartner w = sigma.womanPartner w) /\
        (P.womanPref w (sigma.womanPartner w) (mu.womanPartner w) ->
          lam.womanPartner w = mu.womanPartner w))

theorem matched_woman_partner {M W} (mu : Matching M W) {m : M} {w : W}
    (h : mu.manPartner m = w) : mu.womanPartner w = m := by
  rw [<- h]
  exact mu.left_inv m

theorem matched_man_partner {M W} (mu : Matching M W) {m : M} {w : W}
    (h : mu.womanPartner w = m) : mu.manPartner m = w := by
  rw [<- h]
  exact mu.right_inv w

/- The two forbidden orientations in the sidedness lemma. -/
theorem stablePair_not_mutually_prefer {M W} (P : Profile M W)
    (mu : Matching M W) (hmu : Stable P mu) {m : M} {w : W}
    (hmw : mu.manPartner m ≠ w) :
    Not (P.manPref m w (mu.manPartner m) /\
         P.womanPref w m (mu.womanPartner w)) := by
  intro h
  exact hmu m w h

theorem stablePair_not_old_partners_both_better {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) (mu sigma : Matching M W)
    (hmu : Stable P mu) (hsigma : Stable P sigma)
    {m : M} {w : W} (hsigmaPair : sigma.manPartner m = w)
    (hmuNotPair : mu.manPartner m ≠ w) :
    Not (P.manPref m (mu.manPartner m) w /\
         P.womanPref w (mu.womanPartner w) m) := by
  intro hbad
  obtain ⟨lam, hmen, hwomen⟩ := hjoin mu sigma hmu hsigma
  have hsigW : sigma.womanPartner w = m :=
    matched_woman_partner sigma hsigmaPair
  have hlamM : lam.manPartner m = mu.manPartner m := by
    exact (hmen m).1 (by simpa [hsigmaPair] using hbad.1)
  have hlamW : lam.womanPartner w = m := by
    exact ((hwomen w).1 (by simpa [hsigW] using hbad.2)).trans hsigW
  have : lam.manPartner m = w := matched_man_partner lam hlamW
  exact hmuNotPair (hlamM.symm.trans this)

/- Stable-pair sidedness in a Boolean-free, orientation-exact form. -/
theorem stablePair_sidedness {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) (mu sigma : Matching M W)
    (hmu : Stable P mu) (hsigma : Stable P sigma)
    {m : M} {w : W} (hsigmaPair : sigma.manPartner m = w)
    (hmuNotPair : mu.manPartner m ≠ w) :
    (P.manPref m (mu.manPartner m) w /\
       P.womanPref w m (mu.womanPartner w)) \/
    (P.manPref m w (mu.manPartner m) /\
       P.womanPref w (mu.womanPartner w) m) := by
  have hmChoices := P.man_total m (mu.manPartner m) w hmuNotPair
  have hmuW : mu.womanPartner w ≠ m := by
    intro h
    have := matched_man_partner mu h
    exact hmuNotPair this
  have hwChoices := P.woman_total w (mu.womanPartner w) m hmuW
  rcases hmChoices with hmOld | hmNew <;> rcases hwChoices with hwOld | hwNew
  · exact False.elim
      (stablePair_not_old_partners_both_better P hjoin mu sigma hmu hsigma
        hsigmaPair hmuNotPair <| And.intro hmOld hwOld)
  · exact Or.inl <| And.intro hmOld hwNew
  · exact Or.inr <| And.intro hmNew hwOld
  · exact False.elim
      (stablePair_not_mutually_prefer P mu hmu hmuNotPair <| And.intro hmNew hwNew)

/- Fixing the woman's partner fixes which side of a stable pair the man's
   partner occupies.  The formulation handles the pair case explicitly. -/
theorem fixedPartner_sameSide {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) (sigma mu nu : Matching M W)
    (hsigma : Stable P sigma) (hmu : Stable P mu) (hnu : Stable P nu)
    {m : M} {w : W} (hsigmaPair : sigma.manPartner m = w)
    (hfixed : mu.womanPartner w = nu.womanPartner w)
    (hmuNot : mu.manPartner m ≠ w) (hnuNot : nu.manPartner m ≠ w) :
    (P.manPref m (mu.manPartner m) w <->
       P.manPref m (nu.manPartner m) w) := by
  have smu := stablePair_sidedness P hjoin mu sigma hmu hsigma hsigmaPair hmuNot
  have snu := stablePair_sidedness P hjoin nu sigma hnu hsigma hsigmaPair hnuNot
  rcases smu with smu | smu <;> rcases snu with snu | snu
  · exact Iff.intro (fun _ => snu.1) (fun _ => smu.1)
  · exfalso
    exact (P.woman_asymm w m (mu.womanPartner w) smu.2)
      (by simpa [hfixed] using snu.2)
  · exfalso
    exact (P.woman_asymm w (mu.womanPartner w) m smu.2)
      (by simpa [hfixed] using snu.2)
  · exact Iff.intro (fun h => False.elim ((P.man_asymm m w (mu.manPartner m) smu.1) h))
      (fun h => False.elim ((P.man_asymm m w (nu.manPartner m) snu.1) h))

/- One-sided form used by each endpoint of the revealed interval. -/
theorem revealedBarrier {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) (sigma mu nu : Matching M W)
    (hsigma : Stable P sigma) (hmu : Stable P mu) (hnu : Stable P nu)
    {m p : M} {w : W} (hsigmaPair : sigma.manPartner m = w)
    (hrevealedMu : mu.manPartner p = w)
    (hrevealedNu : nu.manPartner p = w)
    (hmuNot : mu.manPartner m ≠ w) (hnuNot : nu.manPartner m ≠ w) :
    (P.manPref m (mu.manPartner m) w <->
       P.manPref m (nu.manPartner m) w) := by
  apply fixedPartner_sameSide P hjoin sigma mu nu hsigma hmu hnu hsigmaPair
  · calc
      mu.womanPartner w = p := matched_woman_partner mu hrevealedMu
      _ = nu.womanPartner w := (matched_woman_partner nu hrevealedNu).symm
  · exact hmuNot
  · exact hnuNot

end StableMatchings355
