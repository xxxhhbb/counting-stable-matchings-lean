import StableMatchings355.Core

namespace StableMatchings355

/- A ranked list uses smaller natural indices for partners preferred by m. -/
structure RankedPartners {M W : Type} (P : Profile M W) (m : M) (q : Nat) where
  partner : Fin q -> W
  injective : Function.Injective partner
  rank_spec : forall i j, P.manPref m (partner i) (partner j) <-> i.val < j.val

theorem revealed_lower_barrier {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) {m p : M} {q : Nat} (R : RankedPartners P m q)
    (sigma mu nu : Matching M W)
    (hsigma : Stable P sigma) (hmu : Stable P mu) (hnu : Stable P nu)
    {h j t : Fin q}
    (hsigmaPair : sigma.manPartner m = R.partner h)
    (hmuTarget : mu.manPartner m = R.partner j)
    (hnuTarget : nu.manPartner m = R.partner t)
    (hmuReveal : mu.manPartner p = R.partner h)
    (hnuReveal : nu.manPartner p = R.partner h)
    (hhj : h.val < j.val) : h.val < t.val := by
  have hjh : j ≠ h := by
    intro he
    simpa [he] using hhj
  have hpairNe : R.partner j ≠ R.partner h := fun he => hjh (R.injective he)
  have hpm : p ≠ m := by
    intro he
    have : R.partner j = R.partner h := by
      calc
        R.partner j = mu.manPartner m := hmuTarget.symm
        _ = mu.manPartner p := by rw [he]
        _ = R.partner h := hmuReveal
    exact hpairNe this
  have htNe : t ≠ h := by
    intro he
    have hsame : nu.manPartner m = nu.manPartner p := by
      rw [hnuTarget, hnuReveal, he]
    exact hpm (nu.manPartner_injective hsame).symm
  have hmuNot : mu.manPartner m ≠ R.partner h := by simpa [hmuTarget]
  have hnuNot : nu.manPartner m ≠ R.partner h := by
    simpa [hnuTarget] using (fun he : R.partner t = R.partner h => htNe (R.injective he))
  have hsides := fixedPartner_sameSide P hjoin sigma mu nu hsigma hmu hnu
    hsigmaPair
    (by
      calc
        mu.womanPartner (R.partner h) = p := matched_woman_partner mu hmuReveal
        _ = nu.womanPartner (R.partner h) := (matched_woman_partner nu hnuReveal).symm)
    hmuNot hnuNot
  have hnotLeft : Not (P.manPref m (R.partner j) (R.partner h)) := by
    rw [R.rank_spec]
    exact Nat.not_lt_of_ge (Nat.le_of_lt hhj)
  have hnotRight : Not (P.manPref m (R.partner t) (R.partner h)) := by
    intro hpref
    exact hnotLeft (by
      simpa [hmuTarget] using
        (hsides.mpr (by simpa [hnuTarget] using hpref)))
  have hrev : P.manPref m (R.partner h) (R.partner t) := by
    rcases P.man_total m (R.partner h) (R.partner t)
      (fun he => htNe (R.injective he.symm)) with hp | hp
    · exact hp
    · exact False.elim (hnotRight hp)
  exact (R.rank_spec h t).mp hrev

theorem revealed_upper_barrier {M W} (P : Profile M W)
    (hjoin : HasMenJoin P) {m p : M} {q : Nat} (R : RankedPartners P m q)
    (sigma mu nu : Matching M W)
    (hsigma : Stable P sigma) (hmu : Stable P mu) (hnu : Stable P nu)
    {h j t : Fin q}
    (hsigmaPair : sigma.manPartner m = R.partner h)
    (hmuTarget : mu.manPartner m = R.partner j)
    (hnuTarget : nu.manPartner m = R.partner t)
    (hmuReveal : mu.manPartner p = R.partner h)
    (hnuReveal : nu.manPartner p = R.partner h)
    (hjh : j.val < h.val) : t.val < h.val := by
  have hjNe : j ≠ h := by
    intro he
    simpa [he] using hjh
  have hpairNe : R.partner j ≠ R.partner h := fun he => hjNe (R.injective he)
  have hpm : p ≠ m := by
    intro he
    have : R.partner j = R.partner h := by
      calc
        R.partner j = mu.manPartner m := hmuTarget.symm
        _ = mu.manPartner p := by rw [he]
        _ = R.partner h := hmuReveal
    exact hpairNe this
  have htNe : t ≠ h := by
    intro he
    have hsame : nu.manPartner m = nu.manPartner p := by
      rw [hnuTarget, hnuReveal, he]
    exact hpm (nu.manPartner_injective hsame).symm
  have hmuNot : mu.manPartner m ≠ R.partner h := by simpa [hmuTarget]
  have hnuNot : nu.manPartner m ≠ R.partner h := by
    simpa [hnuTarget] using (fun he : R.partner t = R.partner h => htNe (R.injective he))
  have hsides := fixedPartner_sameSide P hjoin sigma mu nu hsigma hmu hnu
    hsigmaPair
    (by
      calc
        mu.womanPartner (R.partner h) = p := matched_woman_partner mu hmuReveal
        _ = nu.womanPartner (R.partner h) := (matched_woman_partner nu hnuReveal).symm)
    hmuNot hnuNot
  have hpref : P.manPref m (R.partner t) (R.partner h) := by
    simpa [hnuTarget] using
      (hsides.mp (by simpa [hmuTarget] using (R.rank_spec j h).mpr hjh))
  exact (R.rank_spec t h).mp hpref

end StableMatchings355
