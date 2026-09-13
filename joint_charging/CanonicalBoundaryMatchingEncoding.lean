import «CanonicalBoundaryGraph»

/-!
# Encoding a canonical rotation frontier as a graph perfect matching

This is the fixed-image fiber bridge used by the deletion double count.  A
set of boundary rotations whose participant pairs cover exactly `S` and form
a perfect matching is injected into perfect matchings of the canonical
boundary graph induced on `S`.
-/

namespace StableMatchingsJointCharging

open StableMatchingsE2E SimpleGraph

noncomputable section

@[ext] structure CanonicalBoundaryMatchingData {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (S : Set (Fin n)) where
  rotations : Finset (CanonicalRotation P)
  subset_boundary : rotations ⊆
    canonicalBoundaryLengthTwoFrontier P hstable base
  support_exact : ∀ m : Fin n, m ∈ S ↔
    ∃ r ∈ rotations, m ∈ canonicalRotationMen P hstable r
  neighbor_unique : ∀ u : S, ∃! v : S,
    u ≠ v ∧ ∃ r ∈ rotations,
      canonicalRotationMen P hstable r =
        ({u.1, v.1} : Finset (Fin n))

def canonicalBoundaryMatchingAdj {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalBoundaryMatchingData P hstable base S) (u v : S) : Prop :=
  u ≠ v ∧ ∃ r ∈ D.rotations,
    canonicalRotationMen P hstable r = ({u.1, v.1} : Finset (Fin n))

theorem canonicalBoundaryMatchingAdj_comm {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalBoundaryMatchingData P hstable base S) (u v : S) :
    canonicalBoundaryMatchingAdj D u v ↔
      canonicalBoundaryMatchingAdj D v u := by
  constructor <;> rintro ⟨hne, r, hr, hpair⟩
  · exact ⟨hne.symm, r, hr, by simpa [Finset.pair_comm] using hpair⟩
  · exact ⟨hne.symm, r, hr, by simpa [Finset.pair_comm] using hpair⟩

def canonicalBoundaryMatchingSubgraph {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalBoundaryMatchingData P hstable base S) :
    ((canonicalBoundaryGraph P hstable base).induce S).Subgraph where
  verts := Set.univ
  Adj := canonicalBoundaryMatchingAdj D
  adj_sub := by
    intro u v h
    have huv : u.1 ≠ v.1 := by
      intro huv
      exact h.1 (Subtype.ext huv)
    obtain ⟨r, hrD, hpair⟩ := h.2
    have hrBoundary := D.subset_boundary hrD
    have hrInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
      P hstable base r).1 hrBoundary
    change (canonicalBoundaryGraph P hstable base).Adj u.1 v.1
    refine ⟨huv, ?_⟩
    rcases hrInfo with hrMax | hrMin
    · exact Or.inl ⟨r,
        (mem_maximalLengthTwoFrontier_iff P hstable base r).2 hrMax,
        hpair⟩
    · exact Or.inr ⟨r,
        (mem_minimalLengthTwoOutsideFrontier_iff P hstable base r).2 hrMin,
        hpair⟩
  edge_vert := by simp
  symm := by
    constructor
    intro u v h
    exact (canonicalBoundaryMatchingAdj_comm D u v).1 h

theorem canonicalBoundaryMatchingSubgraph_isPerfect {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalBoundaryMatchingData P hstable base S) :
    (canonicalBoundaryMatchingSubgraph D).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro u
  exact D.neighbor_unique u

noncomputable def canonicalBoundaryMatchingEncode {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)}
    (D : CanonicalBoundaryMatchingData P hstable base S) :
    PerfectBoundaryMatching
      ((canonicalBoundaryGraph P hstable base).induce S) :=
  ⟨canonicalBoundaryMatchingSubgraph D,
    canonicalBoundaryMatchingSubgraph_isPerfect D⟩

set_option maxHeartbeats 1200000 in
theorem canonicalBoundaryMatchingEncode_injective {n : Nat}
    {P : ProfileCode n} {hstable : (stableSet P).Nonempty}
    {base : CodedStable P} {S : Set (Fin n)} :
    Function.Injective
      (canonicalBoundaryMatchingEncode (P := P) (hstable := hstable)
        (base := base) (S := S)) := by
  classical
  intro D E hencode
  apply CanonicalBoundaryMatchingData.ext
  apply Finset.ext
  intro r
  constructor
  · intro hrD
    have hrBoundary := D.subset_boundary hrD
    have hrInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
      P hstable base r).1 hrBoundary
    have hrLen : canonicalLengthTwo P hstable r := by
      rcases hrInfo with hr | hr <;> exact hr.2
    obtain ⟨a, b, hab, hrpair⟩ := Finset.card_eq_two.mp hrLen
    have haS : a ∈ S := (D.support_exact a).2
      ⟨r, hrD, by simp [hrpair]⟩
    have hbS : b ∈ S := (D.support_exact b).2
      ⟨r, hrD, by simp [hrpair]⟩
    let u : S := ⟨a, haS⟩
    let v : S := ⟨b, hbS⟩
    have hAdjD : canonicalBoundaryMatchingAdj D u v :=
      ⟨by
        intro huv
        exact hab (congrArg Subtype.val huv), r, hrD, hrpair⟩
    have hsubEq : canonicalBoundaryMatchingSubgraph D =
        canonicalBoundaryMatchingSubgraph E :=
      congrArg Subtype.val hencode
    have hAdjEsub : (canonicalBoundaryMatchingSubgraph E).Adj u v := by
      have hAdjDsub : (canonicalBoundaryMatchingSubgraph D).Adj u v := hAdjD
      rw [← hsubEq]
      exact hAdjDsub
    change canonicalBoundaryMatchingAdj E u v at hAdjEsub
    obtain ⟨_, s, hsE, hspair⟩ := hAdjEsub
    have hsBoundary := E.subset_boundary hsE
    let rr : {q : CanonicalRotation P //
        q ∈ canonicalBoundaryLengthTwoFrontier P hstable base} :=
      ⟨r, hrBoundary⟩
    let ss : {q : CanonicalRotation P //
        q ∈ canonicalBoundaryLengthTwoFrontier P hstable base} :=
      ⟨s, hsBoundary⟩
    have hrsSupport : canonicalRotationMen P hstable rr.1 =
        canonicalRotationMen P hstable ss.1 := by
      exact hrpair.trans hspair.symm
    have hrs : rr = ss :=
      canonicalBoundaryRotation_support_injective P hstable base hrsSupport
    have hrsVal : r = s := congrArg Subtype.val hrs
    simpa [hrsVal] using hsE
  · intro hrE
    have hrBoundary := E.subset_boundary hrE
    have hrInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
      P hstable base r).1 hrBoundary
    have hrLen : canonicalLengthTwo P hstable r := by
      rcases hrInfo with hr | hr <;> exact hr.2
    obtain ⟨a, b, hab, hrpair⟩ := Finset.card_eq_two.mp hrLen
    have haS : a ∈ S := (E.support_exact a).2
      ⟨r, hrE, by simp [hrpair]⟩
    have hbS : b ∈ S := (E.support_exact b).2
      ⟨r, hrE, by simp [hrpair]⟩
    let u : S := ⟨a, haS⟩
    let v : S := ⟨b, hbS⟩
    have hAdjE : canonicalBoundaryMatchingAdj E u v :=
      ⟨by
        intro huv
        exact hab (congrArg Subtype.val huv), r, hrE, hrpair⟩
    have hsubEq : canonicalBoundaryMatchingSubgraph D =
        canonicalBoundaryMatchingSubgraph E :=
      congrArg Subtype.val hencode
    have hAdjDsub : (canonicalBoundaryMatchingSubgraph D).Adj u v := by
      have hAdjEsub : (canonicalBoundaryMatchingSubgraph E).Adj u v := hAdjE
      rw [hsubEq]
      exact hAdjEsub
    change canonicalBoundaryMatchingAdj D u v at hAdjDsub
    obtain ⟨_, s, hsD, hspair⟩ := hAdjDsub
    have hsBoundary := D.subset_boundary hsD
    let rr : {q : CanonicalRotation P //
        q ∈ canonicalBoundaryLengthTwoFrontier P hstable base} :=
      ⟨r, hrBoundary⟩
    let ss : {q : CanonicalRotation P //
        q ∈ canonicalBoundaryLengthTwoFrontier P hstable base} :=
      ⟨s, hsBoundary⟩
    have hrsSupport : canonicalRotationMen P hstable rr.1 =
        canonicalRotationMen P hstable ss.1 := by
      exact hrpair.trans hspair.symm
    have hrs : rr = ss :=
      canonicalBoundaryRotation_support_injective P hstable base hrsSupport
    have hrsVal : r = s := congrArg Subtype.val hrs
    simpa [hrsVal] using hsD

noncomputable instance canonicalBoundaryMatchingDataFinite {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (S : Set (Fin n)) :
    Finite (CanonicalBoundaryMatchingData P hstable base S) :=
  Finite.of_injective
    (canonicalBoundaryMatchingEncode
      (P := P) (hstable := hstable) (base := base) (S := S))
    (canonicalBoundaryMatchingEncode_injective
      (P := P) (hstable := hstable) (base := base) (S := S))

theorem natCard_canonicalBoundaryMatchingData_le_two_pow_quarter {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (S : Set (Fin n)) :
    Nat.card (CanonicalBoundaryMatchingData P hstable base S) ≤ 2 ^ (n / 4) := by
  have hencode := Nat.card_le_card_of_injective
    (canonicalBoundaryMatchingEncode (P := P) (hstable := hstable)
      (base := base) (S := S))
    (canonicalBoundaryMatchingEncode_injective
      (P := P) (hstable := hstable) (base := base) (S := S))
  exact hencode.trans
    (canonicalBoundaryGraph_induced_perfectMatching_bound
      P hstable base S)

/-- The set of men covered by a finite family of canonical rotations. -/
def canonicalRotationSupport {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (L : Finset (CanonicalRotation P)) : Set (Fin n) :=
  {m | ∃ r ∈ L, m ∈ canonicalRotationMen P hstable r}

private theorem existsUnique_partner_of_card_eq_two {α : Type*}
    [DecidableEq α] (T : Finset α) (hT : T.card = 2) (u : α) (hu : u ∈ T) :
    ∃! v : α, u ≠ v ∧ T = {u, v} := by
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hT
  rw [hpair] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · refine ⟨b, ⟨hab, hpair⟩, ?_⟩
    intro w hw
    have hbT : b ∈ T := by
      rw [hpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [hw.2] at hbT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbT
    exact (hbT.resolve_left hab.symm).symm
  · refine ⟨a, ⟨hab.symm, ?_⟩, ?_⟩
    · simpa only [Finset.pair_comm] using hpair
    · intro w hw
      have haT : a ∈ T := by
        rw [hpair]
        exact Finset.mem_insert_self _ _
      rw [hw.2] at haT
      simp only [Finset.mem_insert, Finset.mem_singleton] at haT
      exact (haT.resolve_left hab).symm

set_option maxHeartbeats 1200000

/-- A pairwise participant-disjoint family of length-two boundary rotations
is canonically a perfect-matching datum on its exact support. -/
noncomputable def canonicalBoundaryMatchingDataOfDisjoint {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (base : CodedStable P) (L : Finset (CanonicalRotation P))
    (hL : L ⊆ canonicalBoundaryLengthTwoFrontier P hstable base)
    (howner : ∀ r ∈ L, ∀ s ∈ L, ∀ m : Fin n,
      m ∈ canonicalRotationMen P hstable r →
      m ∈ canonicalRotationMen P hstable s → r = s) :
    CanonicalBoundaryMatchingData P hstable base
      (canonicalRotationSupport P hstable L) := by
  classical
  refine
    { rotations := L
      subset_boundary := hL
      support_exact := ?_
      neighbor_unique := ?_ }
  · intro m
    rfl
  · intro u
    obtain ⟨r, hrL, hur⟩ := u.2
    have hrInfo := (mem_canonicalBoundaryLengthTwoFrontier_iff
      P hstable base r).1 (hL hrL)
    have hrLen : canonicalLengthTwo P hstable r := by
      rcases hrInfo with hr | hr <;> exact hr.2
    obtain ⟨v₀, ⟨huv₀, hrpair⟩, hpartnerUnique⟩ :=
      existsUnique_partner_of_card_eq_two
        (canonicalRotationMen P hstable r) hrLen u.1 hur
    have hvSupport : v₀ ∈ canonicalRotationSupport P hstable L := by
      refine ⟨r, hrL, ?_⟩
      rw [hrpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v₀)
    let v : canonicalRotationSupport P hstable L := ⟨v₀, hvSupport⟩
    refine ⟨v, ?_, ?_⟩
    · refine ⟨?_, r, hrL, ?_⟩
      · intro huv
        exact huv₀ (congrArg Subtype.val huv)
      · exact hrpair
    · intro w hw
      obtain ⟨huw, s, hsL, hspair⟩ := hw
      have hus : u.1 ∈ canonicalRotationMen P hstable s := by
        rw [hspair]
        exact Finset.mem_insert_self _ _
      have hrs : r = s := howner r hrL s hsL u.1 hur hus
      have hpairW : canonicalRotationMen P hstable r = {u.1, w.1} := by
        rw [hrs]
        exact hspair
      have huwVal : u.1 ≠ w.1 := by
        intro h
        exact huw (Subtype.ext h)
      have hwVal : w.1 = v₀ :=
        hpartnerUnique w.1 ⟨huwVal, hpairW⟩
      exact Subtype.ext hwVal

set_option maxHeartbeats 200000

/-- The actual maximal length-two frontier is a matching datum after it is
embedded into the boundary of any image stable matching. -/
noncomputable def maximalFrontierBoundaryMatchingData {n : Nat}
    (P : ProfileCode n) (hstable : (stableSet P).Nonempty)
    (source image : CodedStable P)
    (hboundary : maximalLengthTwoFrontier P hstable source ⊆
      canonicalBoundaryLengthTwoFrontier P hstable image) :
    CanonicalBoundaryMatchingData P hstable image
      (canonicalRotationSupport P hstable
        (maximalLengthTwoFrontier P hstable source)) :=
  canonicalBoundaryMatchingDataOfDisjoint P hstable image
    (maximalLengthTwoFrontier P hstable source) hboundary (by
      intro r hr s hs m hmr hms
      exact canonical_maximal_involving_unique P hstable source m
        ((mem_canonicalRotationMen_iff P hstable r m).1 hmr)
        ((mem_canonicalRotationMen_iff P hstable s m).1 hms)
        ((mem_maximalLengthTwoFrontier_iff P hstable source r).1 hr).1
        ((mem_maximalLengthTwoFrontier_iff P hstable source s).1 hs).1)

end

end StableMatchingsJointCharging
