import StableMatchingsE2E.StablePairEquality

namespace StableMatchingsE2E.LabeledMultigraph
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- Original active hyperedges form an isolated binary double on s. -/
def IsOriginalDouble (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (s : Finset V) : Prop :=
  s ⊆ G.vertices ∧ s.card = 2 ∧
    (∀ e ∈ G.edges, ¬Disjoint (H.support e) s → H.support e = s) ∧
    (G.edges.filter (fun e ↦ H.support e = s)).card = 2

/-- Omitted incidences retain the edge label as well as the omitted vertex. -/
def omittedIncidences (G : LabeledMultigraph V E) (H : LabeledHypergraph V E) :
    Finset (E × V) :=
  G.edges.biUnion (fun e ↦ (H.support e \ G.ends e).image (fun w ↦ (e,w)))

@[simp] theorem mem_omittedIncidences (G : LabeledMultigraph V E)
    (H : LabeledHypergraph V E) (e : E) (w : V) :
    (e,w) ∈ G.omittedIncidences H ↔ e ∈ G.edges ∧ w ∈ H.support e ∧ w ∉ G.ends e := by
  simp [omittedIncidences]

/-- Each exceptional component created by shrinking has an omitted incidence
touching its selected pair or one of its vertices. -/
theorem exists_omittedIncidence_touching
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e)
    (hno : ∀ s, ¬G.IsOriginalDouble H s)
    {s : Finset V} (hs : G.IsDoubleComponent s) :
    ∃ e w, (e,w) ∈ G.omittedIncidences H ∧ (G.ends e = s ∨ w ∈ s) := by
  classical
  by_contra hn
  have hnot : ∀ e ∈ G.edges, ∀ w ∈ H.support e, w ∉ G.ends e →
      ¬(G.ends e = s ∨ w ∈ s) := by
    intro e he w hw hwo htouch
    exact hn ⟨e,w,(mem_omittedIncidences G H e w).mpr ⟨he,hw,hwo⟩,htouch⟩
  have hfull : ∀ e ∈ G.edges, G.ends e = s → H.support e = s := by
    intro e he hes
    apply Finset.Subset.antisymm
    · intro w hw
      by_cases hwe : w ∈ G.ends e
      · exact hes ▸ hwe
      · exact False.elim (hnot e he w hw hwe (Or.inl hes))
    · rw [← hes]
      exact hsub e he
  have hiso : ∀ e ∈ G.edges, ¬Disjoint (H.support e) s → H.support e = s := by
    intro e he hmeet
    obtain ⟨w,hw,hws⟩ := Finset.not_disjoint_iff.mp hmeet
    by_cases hwe : w ∈ G.ends e
    · apply hfull e he
      exact hs.2.1.2 e he (Finset.not_disjoint_iff.mpr ⟨w,hwe,hws⟩)
    · exact False.elim (hnot e he w hw hwe (Or.inr hws))
  have hlabels : G.edges.filter (fun e ↦ H.support e = s) = G.edgesOn s := by
    ext e
    simp only [Finset.mem_filter, edgesOn]
    constructor
    · rintro ⟨he,hes⟩
      refine ⟨he,?_⟩
      apply Finset.eq_of_subset_of_card_le
      · exact hes ▸ hsub e he
      · rw [hs.1,G.ends_card e he]
    · rintro ⟨he,hes⟩
      exact ⟨he,hfull e he hes⟩
  exact hno s ⟨hs.2.1.1,hs.1,hiso,by rw [hlabels]; exact hs.2.2⟩

def touchedDoubleComponents (G : LabeledMultigraph V E) (i : E × V) :
    Finset (Finset V) :=
  G.doubleComponents.filter (fun s ↦ G.ends i.1 = s ∨ i.2 ∈ s)

theorem touchedDoubleComponents_card_le_two
    (G : LabeledMultigraph V E) (i : E × V) :
    (G.touchedDoubleComponents i).card ≤ 2 := by
  classical
  have hsource : (G.doubleComponents.filter (fun s ↦ G.ends i.1 = s)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs t ht
    exact (Finset.mem_filter.mp hs).2.symm.trans (Finset.mem_filter.mp ht).2
  have htarget : (G.doubleComponents.filter (fun s ↦ i.2 ∈ s)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs t ht
    have hs' := Finset.mem_filter.mp hs
    have ht' := Finset.mem_filter.mp ht
    by_contra hne
    have hd := disjoint_of_isDoubleComponent G
      ((mem_doubleComponents_iff G s).mp hs'.1).2
      ((mem_doubleComponents_iff G t).mp ht'.1).2 hne
    exact (Finset.disjoint_left.mp hd) hs'.2 ht'.2
  have heq : G.touchedDoubleComponents i =
      (G.doubleComponents.filter (fun s ↦ G.ends i.1 = s)) ∪
      (G.doubleComponents.filter (fun s ↦ i.2 ∈ s)) := by
    ext s
    simp only [touchedDoubleComponents,Finset.mem_filter,Finset.mem_union]
    tauto
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Double-counting the actual omitted incidence set, without disjointness
assumptions on omitted incidences or on original hyperedges. -/
theorem doubleComponentCount_le_twice_omittedIncidences
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e)
    (hno : ∀ s, ¬G.IsOriginalDouble H s) :
    G.doubleComponentCount ≤ 2*(G.omittedIncidences H).card := by
  classical
  have hcover : G.doubleComponents ⊆
      (G.omittedIncidences H).biUnion G.touchedDoubleComponents := by
    intro s hs
    obtain ⟨e,w,hi,ht⟩ := exists_omittedIncidence_touching G H hsub hno
      ((mem_doubleComponents_iff G s).mp hs).2
    exact Finset.mem_biUnion.mpr ⟨(e,w),hi,Finset.mem_filter.mpr ⟨hs,ht⟩⟩
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ G.omittedIncidences H) ↦
    touchedDoubleComponents_card_le_two G i)
  have hcard : ((G.omittedIncidences H).biUnion G.touchedDoubleComponents).card ≤
      ∑ i ∈ G.omittedIncidences H, (G.touchedDoubleComponents i).card := Finset.card_biUnion_le
  have hle := (Finset.card_le_card hcover).trans (hcard.trans hsum)
  simpa [doubleComponentCount,Finset.sum_const,nsmul_eq_mul,Nat.mul_comm] using hle

def excessIncidences (G : LabeledMultigraph V E) (H : LabeledHypergraph V E) : Nat :=
  ∑ e ∈ G.edges, ((H.support e).card-2)

theorem omittedIncidences_card_eq_excess
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e) :
    (G.omittedIncidences H).card = G.excessIncidences H := by
  classical
  have hd : (G.edges : Set E).PairwiseDisjoint
      (fun e ↦ (H.support e \ G.ends e).image (fun w ↦ (e,w))) := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨w,hw,hi⟩ := Finset.mem_image.mp hi
    obtain ⟨v,hv,hj⟩ := Finset.mem_image.mp hj
    exact hef (congrArg Prod.fst (hi.trans hj.symm))
  unfold omittedIncidences excessIncidences
  rw [Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.card_image_of_injective _ (fun w v h ↦ congrArg Prod.snd h),
    Finset.card_sdiff_of_subset (hsub e he),G.ends_card e he]

theorem doubleComponentCount_le_twice_excess
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e)
    (hno : ∀ s, ¬G.IsOriginalDouble H s) :
    G.doubleComponentCount ≤ 2*G.excessIncidences H := by
  have h := doubleComponentCount_le_twice_omittedIncidences G H hsub hno
  rwa [omittedIncidences_card_eq_excess G H hsub] at h

/-- Matchings of the original hypergraph restricted to the active labels. -/
def originalMatchingFamily (G : LabeledMultigraph V E) (H : LabeledHypergraph V E) :
    Finset (Finset E) := G.edges.powerset.filter H.IsMatching

theorem originalMatchingFamily_subset
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e) :
    G.originalMatchingFamily H ⊆ G.matchingFamily := by
  intro S hS
  have hS' := Finset.mem_filter.mp hS
  have hactive := Finset.mem_powerset.mp hS'.1
  apply (mem_matchingFamily_iff G S).mpr
  refine ⟨hactive,?_⟩
  intro e he f hf hef
  exact (hS'.2 e he f hf hef).mono (hsub e (hactive he)) (hsub f (hactive hf))

theorem originalMatchingCount_le
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e) :
    (G.originalMatchingFamily H).card ≤ G.matchingCount :=
  Finset.card_le_card (originalMatchingFamily_subset G H hsub)

theorem original_incidence_cost
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e) :
    G.vertexCount + ∑ e ∈ G.edges, (H.support e).card =
      G.vertexCount + 2*G.edgeCount + G.excessIncidences H := by
  have heach : ∀ e ∈ G.edges, (H.support e).card = 2+((H.support e).card-2) := by
    intro e he
    have hle := Finset.card_le_card (hsub e he)
    rw [G.ends_card e he] at hle
    omega
  rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib]
  simp [Finset.sum_const,edgeCount,excessIncidences,Nat.mul_comm,Nat.add_assoc]

/-- Integer fourth-power version of the hypergraph shrinking bound, retaining
the exact excess-incidence penalty. -/
theorem originalMatching_fourth_bound
    (G : LabeledMultigraph V E) (H : LabeledHypergraph V E)
    (hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e)
    (hno : ∀ s, ¬G.IsOriginalDouble H s) :
    (G.originalMatchingFamily H).card^4 * 8192^(G.excessIncidences H) ≤
      2^(G.vertexCount + ∑ e ∈ G.edges, (H.support e).card) * 6561^(G.excessIncidences H) := by
  have ht := StablePairCoefficients.t_pos
  have hq := doubleComponentCount_le_twice_excess G H hsub hno
  have hn := (sharpBound_iff_normalized G).mp (sharpBound G)
  have hn' := hn.trans (pow_le_pow_right₀ StablePairCoefficients.gamma_gt_one.le hq)
  have hi := (StablePairCoefficients.integer_bound_iff_normalized G.matchingCount
    (G.vertexCount+2*G.edgeCount) (2*G.excessIncidences H)).mpr hn'
  have hmul := Nat.mul_le_mul_left (2^(G.excessIncidences H)) hi
  have h8192 : 2^(G.excessIncidences H)*64^(2*G.excessIncidences H) =
      8192^(G.excessIncidences H) := by
    rw [pow_mul, ← mul_pow]
    norm_num
  have h6561 : 81^(2*G.excessIncidences H) = 6561^(G.excessIncidences H) := by
    rw [pow_mul]
    norm_num
  have hgraph : G.matchingCount^4*8192^(G.excessIncidences H) ≤
      2^(G.vertexCount+2*G.edgeCount+G.excessIncidences H)*6561^(G.excessIncidences H) := by
    rw [← h8192,pow_add,← h6561]
    convert hmul using 1 <;> ring
  rw [original_incidence_cost G H hsub]
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (originalMatchingCount_le G H hsub) 4)).trans hgraph

end StableMatchingsE2E.LabeledMultigraph

namespace StableMatchingsE2E.LabeledHypergraph
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

def IsIsolatedDouble (H : LabeledHypergraph V E) (s : Finset V) : Prop :=
  s.card = 2 ∧ (∀ e, ¬Disjoint (H.support e) s → H.support e = s) ∧
    (Finset.univ.filter (fun e ↦ H.support e = s)).card = 2

/-- The full labeled-hypergraph bound. Pair choices are constructed in the
proof; they are not an extra assumption of the theorem. -/
theorem matchingCount_fourth_bound
    (H : LabeledHypergraph V E) (vertices : Finset V)
    (hinside : ∀ e, H.support e ⊆ vertices)
    (hsize : ∀ e, 2 ≤ (H.support e).card)
    (hno : ∀ s, ¬H.IsIsolatedDouble s) :
    H.matchingCount^4 * 8192^(∑ e, ((H.support e).card-2)) ≤
      2^(vertices.card + ∑ e, (H.support e).card) * 6561^(∑ e, ((H.support e).card-2)) := by
  classical
  choose p hpSub hpCard using (fun e ↦ Finset.exists_subset_card_eq (hsize e))
  let G : LabeledMultigraph V E := {
    vertices := vertices
    edges := Finset.univ
    ends := p
    ends_card := fun e _ ↦ hpCard e
    ends_subset := fun e _ ↦ (hpSub e).trans (hinside e) }
  have hsub : ∀ e ∈ G.edges, G.ends e ⊆ H.support e := fun e _ ↦ hpSub e
  have hnoG : ∀ s, ¬G.IsOriginalDouble H s := by
    intro s hs
    exact hno s ⟨hs.2.1,fun e hm ↦ hs.2.2.1 e (Finset.mem_univ e) hm,hs.2.2.2⟩
  have hf : G.originalMatchingFamily H = H.matchingFamily := by
    ext S
    simp [LabeledMultigraph.originalMatchingFamily,matchingFamily,G]
  have hb := LabeledMultigraph.originalMatching_fourth_bound G H hsub hnoG
  rw [hf] at hb
  simpa [matchingCount,LabeledMultigraph.excessIncidences,LabeledMultigraph.vertexCount,G] using hb

/-- Dropping the penalty gives the sharp unpenalized fourth-power bound. -/
theorem matchingCount_fourth_le_two_pow
    (H : LabeledHypergraph V E) (vertices : Finset V)
    (hinside : ∀ e, H.support e ⊆ vertices)
    (hsize : ∀ e, 2 ≤ (H.support e).card)
    (hno : ∀ s, ¬H.IsIsolatedDouble s) :
    H.matchingCount^4 ≤ 2^(vertices.card + ∑ e, (H.support e).card) := by
  have hb := matchingCount_fourth_bound H vertices hinside hsize hno
  have hp : 6561^(∑ e, ((H.support e).card-2)) ≤
      8192^(∑ e, ((H.support e).card-2)) := Nat.pow_le_pow_left (by decide) _
  have hh := hb.trans (Nat.mul_le_mul_left _ hp)
  exact Nat.le_of_mul_le_mul_right hh (by positivity)

/-- Equality at the unpenalized bound forces every hyperedge to be binary. -/
theorem all_binary_of_matchingCount_fourth_eq
    (H : LabeledHypergraph V E) (vertices : Finset V)
    (hinside : ∀ e, H.support e ⊆ vertices)
    (hsize : ∀ e, 2 ≤ (H.support e).card)
    (hno : ∀ s, ¬H.IsIsolatedDouble s)
    (heq : H.matchingCount^4 = 2^(vertices.card + ∑ e, (H.support e).card)) :
    ∀ e, (H.support e).card = 2 := by
  have hb := matchingCount_fourth_bound H vertices hinside hsize hno
  rw [heq] at hb
  have hbase : 0 < 2^(vertices.card + ∑ e, (H.support e).card) := by positivity
  have hpow := Nat.le_of_mul_le_mul_left hb hbase
  have hzero : (∑ e, ((H.support e).card-2)) = 0 := by
    by_contra hn
    have hp : 6561^(∑ e, ((H.support e).card-2)) <
        8192^(∑ e, ((H.support e).card-2)) := Nat.pow_lt_pow_left (by decide) hn
    omega
  intro e
  have hs : (H.support e).card-2 = 0 :=
    (Finset.sum_eq_zero_iff.mp hzero) e (Finset.mem_univ e)
  have hge := hsize e
  omega

end StableMatchingsE2E.LabeledHypergraph
