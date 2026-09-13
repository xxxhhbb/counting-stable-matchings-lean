import «StableLatticeBridge»
import StableMatchingsE2E.StableEntropyApplication

/-!
# Canonical rotation boundary states and participant chains

For a Birkhoff generator `r`, the strict and closed principal lower sets
encode the stable matching immediately before and after adding `r`.  A man is
said to participate when his partner changes across these two genuine stable
matchings.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E

noncomputable section

def strictRotationLowerSet {n : Nat} {P : ProfileCode n}
    (r : CanonicalRotation P) : LowerSet (CanonicalRotation P) where
  carrier := {s | s < r}
  lower' := by
    intro a b hab hb
    exact hab.trans_lt hb

def closedRotationLowerSet {n : Nat} {P : ProfileCode n}
    (r : CanonicalRotation P) : LowerSet (CanonicalRotation P) where
  carrier := {s | s ≤ r}
  lower' := by
    intro a b hab hb
    exact hab.trans hb

theorem strictRotationLowerSet_lt_closed {n : Nat} {P : ProfileCode n}
    (r : CanonicalRotation P) :
    strictRotationLowerSet r < closedRotationLowerSet r := by
  apply lt_of_le_of_ne
  · intro s hs
    change s < r at hs
    change s ≤ r
    exact hs.le
  · intro heq
    have hr : r ∈ closedRotationLowerSet r := by
      change r ≤ r
      exact le_rfl
    have : r ∈ strictRotationLowerSet r := by
      rw [heq]
      exact hr
    change r < r at this
    exact (lt_irrefl r) this

def rotationBefore {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    CodedStable P :=
  (stableBirkhoffLowerSet P hstable).symm (strictRotationLowerSet r)

def rotationAfter {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    CodedStable P :=
  (stableBirkhoffLowerSet P hstable).symm (closedRotationLowerSet r)

theorem rotationBefore_lt_after {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    rotationBefore P hstable r < rotationAfter P hstable r := by
  exact (stableBirkhoffLowerSet P hstable).symm.lt_iff_lt.mpr
    (strictRotationLowerSet_lt_closed r)

theorem rotationAfter_eq_generator {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    rotationAfter P hstable r = r.1 := by
  let e := stableBirkhoffLowerSet P hstable
  apply e.injective
  rw [show e (rotationAfter P hstable r) = closedRotationLowerSet r by
    exact e.apply_symm_apply (closedRotationLowerSet r)]
  ext s
  change s ≤ r ↔ s.1 ≤ r.1
  rfl

@[simp] theorem mem_rotationIdeal_rotationAfter_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (r t : CanonicalRotation P) :
    t ∈ stableRotationIdeal P hstable (rotationAfter P hstable r) ↔ t ≤ r := by
  rw [mem_stableRotationIdeal_iff, rotationAfter_eq_generator]
  rfl

set_option maxHeartbeats 800000 in
@[simp] theorem mem_rotationIdeal_rotationBefore_iff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (r t : CanonicalRotation P) :
    t ∈ stableRotationIdeal P hstable (rotationBefore P hstable r) ↔ t < r := by
  rw [mem_stableRotationIdeal_iff]
  let e := stableBirkhoffLowerSet P hstable
  rw [← rotationAfter_eq_generator P hstable t]
  change e.symm (closedRotationLowerSet t) ≤
      e.symm (strictRotationLowerSet r) ↔ t < r
  rw [e.symm.le_iff_le]
  constructor
  · intro h
    have ht : t ∈ closedRotationLowerSet t := by
      change t ≤ t
      exact le_rfl
    exact h ht
  · intro h s hs
    change s ≤ t at hs
    change s < r
    exact hs.trans_lt h

def canonicalRotationInvolvesMan {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (m : Fin n)
    (r : CanonicalRotation P) : Prop :=
  (rotationBefore P hstable r).1 m ≠ (rotationAfter P hstable r).1 m

def canonicalRotationMen {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (canonicalRotationInvolvesMan P hstable · r)

@[simp] theorem mem_canonicalRotationMen_iff {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) (m : Fin n) :
    m ∈ canonicalRotationMen P hstable r ↔
      canonicalRotationInvolvesMan P hstable m r := by
  simp [canonicalRotationMen]

theorem equiv_differs_at_second_coordinate {n : Nat}
    (f g : Equiv.Perm (Fin n)) (m : Fin n) (hm : f m ≠ g m) :
    ∃ p : Fin n, p ≠ m ∧ f p ≠ g p := by
  let p := g.symm (f m)
  have hgp : g p = f m := g.apply_symm_apply (f m)
  have hpm : p ≠ m := by
    intro h
    exact hm (hgp.symm.trans (congrArg g h))
  refine ⟨p, hpm, ?_⟩
  intro hfg
  have hfp : f p = f m := hfg.trans hgp
  exact hpm (f.injective hfp)

set_option maxHeartbeats 800000 in
/-- Every canonical rotation moves at least two men.  This is forced already
by the two endpoint matchings being distinct permutations; no classical
rotation-size theorem is assumed. -/
theorem two_le_card_canonicalRotationMen {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (r : CanonicalRotation P) :
    2 ≤ (canonicalRotationMen P hstable r).card := by
  classical
  have hne : rotationBefore P hstable r ≠ rotationAfter P hstable r :=
    (rotationBefore_lt_after P hstable r).ne
  have hex : ∃ m : Fin n, canonicalRotationInvolvesMan P hstable m r := by
    by_contra hall
    push Not at hall
    apply hne
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact not_ne_iff.mp (hall x)
  obtain ⟨m, hm⟩ := hex
  obtain ⟨p, hpm, hp⟩ := equiv_differs_at_second_coordinate
    (rotationBefore P hstable r).1 (rotationAfter P hstable r).1 m hm
  have hsub : ({m, p} : Finset (Fin n)) ⊆ canonicalRotationMen P hstable r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxm | hxp
    · subst x
      exact (mem_canonicalRotationMen_iff P hstable r m).2 hm
    · subst x
      exact (mem_canonicalRotationMen_iff P hstable r p).2 hp
  calc
    2 = ({m, p} : Finset (Fin n)).card := by simp [Ne.symm hpm]
    _ ≤ (canonicalRotationMen P hstable r).card := Finset.card_le_card hsub

theorem involved_manRank_strict {n : Nat} (P : ProfileCode n)
    (hstable : (stableSet P).Nonempty) (m : Fin n)
    (r : CanonicalRotation P) (hr : canonicalRotationInvolvesMan P hstable m r) :
    P.manRank m ((rotationAfter P hstable r).1 m) <
      P.manRank m ((rotationBefore P hstable r).1 m) := by
  have hle := (rotationBefore_lt_after P hstable r).le m
  exact lt_of_le_of_ne hle (fun heq ↦ hr ((P.manRank m).injective heq.symm))

theorem inf_closedRotationLowerSet_le_strict_left {n : Nat}
    {P : ProfileCode n} {r s : CanonicalRotation P}
    (hrs : ¬ r ≤ s) :
    closedRotationLowerSet r ⊓ closedRotationLowerSet s ≤
      strictRotationLowerSet r := by
  intro t ht
  change t ≤ r ∧ t ≤ s at ht
  change t < r
  exact lt_of_le_of_ne ht.1 (by
    intro htr
    subst t
    exact hrs ht.2)

theorem inf_rotationAfter_le_before_left {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    {r s : CanonicalRotation P} (hrs : ¬ r ≤ s) :
    rotationAfter P hstable r ⊓ rotationAfter P hstable s ≤
      rotationBefore P hstable r := by
  let e := stableBirkhoffLowerSet P hstable
  calc
    rotationAfter P hstable r ⊓ rotationAfter P hstable s =
        e.symm (closedRotationLowerSet r ⊓ closedRotationLowerSet s) := by
      exact (map_inf e.symm (closedRotationLowerSet r)
        (closedRotationLowerSet s)).symm
    _ ≤ e.symm (strictRotationLowerSet r) :=
      e.symm.monotone (inf_closedRotationLowerSet_le_strict_left hrs)
    _ = rotationBefore P hstable r := rfl

theorem inf_closedRotationLowerSet_le_strict_of_not_mem {n : Nat}
    {P : ProfileCode n} {r : CanonicalRotation P}
    (T : LowerSet (CanonicalRotation P)) (hrT : r ∉ T) :
    closedRotationLowerSet r ⊓ T ≤ strictRotationLowerSet r := by
  intro t ht
  change t ≤ r ∧ t ∈ T at ht
  change t < r
  exact lt_of_le_of_ne ht.1 (by
    intro htr
    subst t
    exact hrT ht.2)

theorem inf_rotationAfter_matching_le_before_of_not_mem {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu : CodedStable P) (r : CanonicalRotation P)
    (hr : r ∉ stableRotationIdeal P hstable mu) :
    rotationAfter P hstable r ⊓ mu ≤ rotationBefore P hstable r := by
  let e := stableBirkhoffLowerSet P hstable
  have hrImage : r ∉ e mu := by
    intro hrmem
    apply hr
    exact (mem_stableRotationIdeal_iff P hstable mu r).2 hrmem
  calc
    rotationAfter P hstable r ⊓ mu =
        e.symm (closedRotationLowerSet r) ⊓ e.symm (e mu) := by
      rw [rotationAfter, e.symm_apply_apply]
    _ = e.symm (closedRotationLowerSet r ⊓ e mu) := by
      exact (map_inf e.symm (closedRotationLowerSet r) (e mu)).symm
    _ ≤ e.symm (strictRotationLowerSet r) :=
      e.symm.monotone
        (inf_closedRotationLowerSet_le_strict_of_not_mem (e mu) hrImage)
    _ = rotationBefore P hstable r := rfl

theorem not_mem_involved_manRank_strict {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu : CodedStable P) (m : Fin n) (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable m r)
    (hr : r ∉ stableRotationIdeal P hstable mu) :
    P.manRank m ((rotationAfter P hstable r).1 m) <
      P.manRank m (mu.1 m) := by
  have hmeet := inf_rotationAfter_matching_le_before_of_not_mem
    P hstable mu r hr
  have hrank := hmeet m
  rw [manRank_inf] at hrank
  have hstrict := involved_manRank_strict P hstable m r hinv
  by_contra hnot
  have hmule : P.manRank m (mu.1 m) ≤
      P.manRank m ((rotationAfter P hstable r).1 m) := le_of_not_gt hnot
  have hpredle : P.manRank m ((rotationBefore P hstable r).1 m) ≤
      P.manRank m ((rotationAfter P hstable r).1 m) := by
    simpa [max_eq_left hmule] using hrank
  exact (not_lt_of_ge hpredle) hstrict

theorem mem_rotationIdeal_iff_manRank_le_after_of_involves {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu : CodedStable P) (m : Fin n) (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable m r) :
    r ∈ stableRotationIdeal P hstable mu ↔
      P.manRank m (mu.1 m) ≤
        P.manRank m ((rotationAfter P hstable r).1 m) := by
  constructor
  · intro hr
    have hle : rotationAfter P hstable r ≤ mu := by
      rw [rotationAfter_eq_generator]
      exact (mem_stableRotationIdeal_iff P hstable mu r).1 hr
    exact hle m
  · intro hrank
    by_contra hr
    have hlt := not_mem_involved_manRank_strict P hstable mu m r hinv hr
    exact (not_lt_of_ge hrank) hlt

theorem rotationIdeal_membership_iff_of_same_man_partner {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu nu : CodedStable P) (m : Fin n) (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable m r)
    (hpartner : mu.1 m = nu.1 m) :
    r ∈ stableRotationIdeal P hstable mu ↔
      r ∈ stableRotationIdeal P hstable nu := by
  rw [mem_rotationIdeal_iff_manRank_le_after_of_involves P hstable mu m r hinv,
    mem_rotationIdeal_iff_manRank_le_after_of_involves P hstable nu m r hinv,
    hpartner]

/-- Exact profile-level reveal-fiber bridge: revealing one participant's
partner fixes membership of every canonical rotation involving that
participant. -/
theorem involved_rotation_forced_in_stableFiber {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (nu : MatchingCode n)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (p : Fin n) (r : CanonicalRotation P)
    (hinv : canonicalRotationInvolvesMan P hstable p r)
    (hrBase : r ∈ stableRotationIdeal P hstable base)
    (hp : revealed p)
    (hnu : nu ∈ stableFiber P base.1 revealed) :
    r ∈ stableRotationIdeal P hstable
      (⟨nu, (mem_stableFiber_iff P base.1 nu revealed).1 hnu |>.1⟩ : CodedStable P) := by
  let nuStable : CodedStable P :=
    ⟨nu, (mem_stableFiber_iff P base.1 nu revealed).1 hnu |>.1⟩
  have hpartner : base.1 p = nuStable.1 p :=
    ((mem_stableFiber_iff P base.1 nu revealed).1 hnu).2 p hp |>.symm
  exact (rotationIdeal_membership_iff_of_same_man_partner
    P hstable base nuStable p r hinv hpartner).1 hrBase

/-- If a revealed participant certifies a later included rotation, ideal
closure also certifies every earlier rotation.  This is the precise
nonmaximal extra-left witness used by the local support charge. -/
theorem earlier_rotation_forced_in_stableFiber {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (nu : MatchingCode n)
    (revealed : Fin n → Prop) [DecidablePred revealed]
    (p : Fin n) (r s : CanonicalRotation P)
    (hrs : r ≤ s)
    (hinvS : canonicalRotationInvolvesMan P hstable p s)
    (hsBase : s ∈ stableRotationIdeal P hstable base)
    (hp : revealed p)
    (hnu : nu ∈ stableFiber P base.1 revealed) :
    r ∈ stableRotationIdeal P hstable
      (⟨nu, (mem_stableFiber_iff P base.1 nu revealed).1 hnu |>.1⟩ : CodedStable P) := by
  let nuStable : CodedStable P :=
    ⟨nu, (mem_stableFiber_iff P base.1 nu revealed).1 hnu |>.1⟩
  have hsNu : s ∈ stableRotationIdeal P hstable nuStable :=
    involved_rotation_forced_in_stableFiber P hstable base nu revealed p s
      hinvS hsBase hp hnu
  exact stableRotationIdeal_isIdeal P hstable nuStable hrs hsNu

/-- Canonical rotations involving the same man form a chain.  The proof is
purely lattice-theoretic after the profile-level stable lattice has been
constructed: two incomparable generators would each force a strict rank
drop, while their meet is simultaneously below both predecessor states,
contradicting the `max` formula for the meet rank. -/
theorem canonicalRotations_involving_man_comparable {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (m : Fin n) {r s : CanonicalRotation P}
    (hr : canonicalRotationInvolvesMan P hstable m r)
    (hs : canonicalRotationInvolvesMan P hstable m s) :
    r ≤ s ∨ s ≤ r := by
  by_contra hcomp
  push Not at hcomp
  have hmeetR := inf_rotationAfter_le_before_left P hstable hcomp.1
  have hmeetS := inf_rotationAfter_le_before_left P hstable hcomp.2
  have hrankR := hmeetR m
  have hrankS := hmeetS m
  rw [manRank_inf] at hrankR hrankS
  have hstrictR := involved_manRank_strict P hstable m r hr
  have hstrictS := involved_manRank_strict P hstable m s hs
  by_cases hars :
      P.manRank m ((rotationAfter P hstable r).1 m) ≤
        P.manRank m ((rotationAfter P hstable s).1 m)
  · have hpsle :
        P.manRank m ((rotationBefore P hstable s).1 m) ≤
          P.manRank m ((rotationAfter P hstable s).1 m) := by
      simpa [max_eq_left hars] using hrankS
    exact (not_lt_of_ge hpsle) hstrictS
  · have hasr :
        P.manRank m ((rotationAfter P hstable s).1 m) ≤
          P.manRank m ((rotationAfter P hstable r).1 m) :=
      le_of_not_ge hars
    have hprle :
        P.manRank m ((rotationBefore P hstable r).1 m) ≤
          P.manRank m ((rotationAfter P hstable r).1 m) := by
      simpa [max_eq_left hasr] using hrankR
    exact (not_lt_of_ge hprle) hstrictR

set_option maxHeartbeats 1200000 in
/-- A strict improvement of one man's partner between two comparable stable
matchings is witnessed by a canonical Birkhoff rotation in the ideal
difference which genuinely moves that man.  This is the context-independence
bridge needed to turn principal before/after supports into supports along an
arbitrary elimination path. -/
theorem exists_involving_rotation_in_ideal_diff_of_partner_ne {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu nu : CodedStable P) (m : Fin n) (hmunu : mu ≤ nu)
    (hne : mu.1 m ≠ nu.1 m) :
    ∃ r : CanonicalRotation P,
      r ∉ stableRotationIdeal P hstable mu ∧
      r ∈ stableRotationIdeal P hstable nu ∧
      canonicalRotationInvolvesMan P hstable m r := by
  classical
  let mu0 := Classical.choose hstable
  have hmu0 : mu0 ∈ stableSet P := Classical.choose_spec hstable
  letI : Nonempty (CodedStable P) :=
    ⟨⟨mu0, (mem_stableSet_iff P mu0).1 hmu0⟩⟩
  letI : OrderBot (CodedStable P) := Fintype.toOrderBot _
  have hrank : P.manRank m (nu.1 m) < P.manRank m (mu.1 m) :=
    lt_of_le_of_ne (hmunu m) (fun h ↦ hne ((P.manRank m).injective h.symm))
  have rank_le_finset_sup : ∀ (s : Finset (CodedStable P)),
      (∀ b ∈ s, P.manRank m (mu.1 m) ≤ P.manRank m (b.1 m)) →
      P.manRank m (mu.1 m) ≤ P.manRank m ((s.sup id).1 m) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        exact (show (⊥ : CodedStable P) ≤ mu from bot_le) m
    | @insert b s hb ih =>
        intro hall
        rw [Finset.sup_insert, manRank_sup]
        apply le_min
        · exact hall b (Finset.mem_insert_self b s)
        · apply ih
          intro c hc
          exact hall c (Finset.mem_insert_of_mem hc)
  have exists_low_irred : ∀ x : CodedStable P,
      P.manRank m (x.1 m) < P.manRank m (mu.1 m) →
      ∃ r : CanonicalRotation P,
        r.1 ≤ x ∧ P.manRank m (r.1.1 m) < P.manRank m (mu.1 m) := by
    intro x hx
    obtain ⟨s, hsup, hirred⟩ := exists_supIrred_decomposition x
    have hex : ∃ b ∈ s,
        P.manRank m (b.1 m) < P.manRank m (mu.1 m) := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ b ∈ s,
          P.manRank m (mu.1 m) ≤ P.manRank m (b.1 m) := by
        intro b hb
        exact hnone b hb
      have hle := rank_le_finset_sup s hall
      rw [hsup] at hle
      exact (not_lt_of_ge hle) hx
    obtain ⟨b, hb, hblow⟩ := hex
    let r : CanonicalRotation P := ⟨b, hirred hb⟩
    refine ⟨r, ?_, hblow⟩
    exact (Finset.le_sup (f := id) hb).trans_eq hsup
  have descend : ∀ r : CanonicalRotation P,
      P.manRank m (r.1.1 m) < P.manRank m (mu.1 m) →
      ∃ s : CanonicalRotation P,
        s ≤ r ∧ canonicalRotationInvolvesMan P hstable m s ∧
          P.manRank m (s.1.1 m) < P.manRank m (mu.1 m) := by
    intro r
    induction r using WellFoundedLT.induction with
    | ind r ih =>
        intro hrlow
        by_cases hrm : canonicalRotationInvolvesMan P hstable m r
        · exact ⟨r, le_rfl, hrm, hrlow⟩
        · have heq : (rotationBefore P hstable r).1 m = r.1.1 m := by
            have h := not_ne_iff.mp hrm
            simpa [canonicalRotationInvolvesMan,
              rotationAfter_eq_generator] using h
          have hbeforelow :
              P.manRank m ((rotationBefore P hstable r).1 m) <
                P.manRank m (mu.1 m) := by
            simpa [heq] using hrlow
          obtain ⟨s, hsBefore, hslow⟩ :=
            exists_low_irred (rotationBefore P hstable r) hbeforelow
          have hsr : s < r := by
            have hslt : s.1 < r.1 :=
              hsBefore.trans_lt (by
                simpa [rotationAfter_eq_generator] using
                  (rotationBefore_lt_after P hstable r))
            exact hslt
          obtain ⟨t, hts, htm, htlow⟩ := ih s hsr hslow
          exact ⟨t, hts.trans hsr.le, htm, htlow⟩
  obtain ⟨r, hrnu, hrlow⟩ := exists_low_irred nu hrank
  obtain ⟨s, hsr, hsm, hslow⟩ := descend r hrlow
  have hsnu : s.1 ≤ nu := (show s.1 ≤ r.1 from hsr).trans hrnu
  have hsnmu : ¬ s.1 ≤ mu := by
    intro hsmu
    exact (not_lt_of_ge (hsmu m)) hslow
  exact ⟨s,
    fun hs ↦ hsnmu ((mem_stableRotationIdeal_iff P hstable mu s).1 hs),
    (mem_stableRotationIdeal_iff P hstable nu s).2 hsnu,
    hsm⟩

/-- If no canonical rotation between two comparable ideals moves a man,
then that man's partner is unchanged. -/
theorem man_partner_eq_of_no_involving_rotation_in_ideal_diff {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (mu nu : CodedStable P) (m : Fin n) (hmunu : mu ≤ nu)
    (hnone : ∀ r : CanonicalRotation P,
      r ∈ stableRotationIdeal P hstable nu →
      r ∉ stableRotationIdeal P hstable mu →
      ¬ canonicalRotationInvolvesMan P hstable m r) :
    mu.1 m = nu.1 m := by
  by_contra hne
  obtain ⟨r, hrmu, hrnu, hrm⟩ :=
    exists_involving_rotation_in_ideal_diff_of_partner_ne
      P hstable mu nu m hmunu hne
  exact hnone r hrnu hrmu hrm

end

end StableMatchingsJointCharging
