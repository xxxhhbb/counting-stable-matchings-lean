import StableMatchings355.FullInterval

namespace StableMatchingsE2E

open StableMatchings355

/-!
The stable partners in an exact enumeration are women.  Relative to a fixed
base matching, each such woman has a unique male owner.  These owners are the
actual independent priority coordinates consumed by the two-sided marker
argument.  Keeping the owner map explicit prevents an unjustified switch from
"distinct women" to "independent men" later in the probability proof.
-/

def stablePartnerOwner {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (h : Fin q) : Fin n :=
  base.womanPartner (E.ranked.partner h)

@[simp] theorem manPartner_stablePartnerOwner {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (h : Fin q) :
    base.manPartner (stablePartnerOwner E base h) = E.ranked.partner h := by
  exact base.right_inv (E.ranked.partner h)

theorem stablePartnerOwner_injective {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) :
    Function.Injective (stablePartnerOwner E base) := by
  intro h k howner
  apply E.ranked.injective
  calc
    E.ranked.partner h = base.manPartner (stablePartnerOwner E base h) :=
      (manPartner_stablePartnerOwner E base h).symm
    _ = base.manPartner (stablePartnerOwner E base k) := congrArg base.manPartner howner
    _ = E.ranked.partner k := manPartner_stablePartnerOwner E base k

theorem stablePartnerOwner_ne_target {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) {j h : Fin q}
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (hhj : h ≠ j) :
    stablePartnerOwner E base h ≠ target := by
  intro howner
  apply hhj
  apply E.ranked.injective
  calc
    E.ranked.partner h = base.manPartner (stablePartnerOwner E base h) :=
      (manPartner_stablePartnerOwner E base h).symm
    _ = base.manPartner target := congrArg base.manPartner howner
    _ = E.ranked.partner j := hbaseTarget

theorem marker_owner_unique {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    {h : Fin q} {p : Fin n}
    (hm : IsRevealedMarker E base revealed h p) :
    p = stablePartnerOwner E base h := by
  apply base.manPartner_injective
  calc
    base.manPartner p = E.ranked.partner h := hm.2
    _ = base.manPartner (stablePartnerOwner E base h) :=
      (manPartner_stablePartnerOwner E base h).symm

theorem marker_at_owner_iff {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    (h : Fin q) :
    IsRevealedMarker E base revealed h (stablePartnerOwner E base h) ↔
      revealed (stablePartnerOwner E base h) := by
  constructor
  · exact fun hm => hm.1
  · intro hr
    exact ⟨hr, manPartner_stablePartnerOwner E base h⟩

end StableMatchingsE2E
