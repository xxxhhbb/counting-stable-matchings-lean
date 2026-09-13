import StableMatchingsE2E.StablePairMultigraph

namespace StableMatchingsE2E.LabeledMultigraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- Restrict active labels while keeping the ambient vertices and endpoints. -/
def restrictEdges (G : LabeledMultigraph V E) (A : Finset E) :
    LabeledMultigraph V E where
  vertices := G.vertices
  edges := G.edges ∩ A
  ends := G.ends
  ends_card := fun e he ↦ G.ends_card e (Finset.mem_inter.1 he).1
  ends_subset := fun e he ↦ G.ends_subset e (Finset.mem_inter.1 he).1

theorem restrictEdges_isMatching_iff
    (G : LabeledMultigraph V E) (A S : Finset E) :
    (G.restrictEdges A).IsMatching S ↔ G.IsMatching S ∧ S ⊆ A := by
  change (S ⊆ G.edges ∩ A ∧ G.toHypergraph.IsMatching S) ↔
    (S ⊆ G.edges ∧ G.toHypergraph.IsMatching S) ∧ S ⊆ A
  rw [Finset.subset_inter_iff]
  tauto

theorem matching_subset (G : LabeledMultigraph V E)
    {S T : Finset E} (hS : G.IsMatching S) (hT : T ⊆ S) : G.IsMatching T := by
  refine ⟨hT.trans hS.1, ?_⟩
  intro e he f hf hef
  exact hS.2 e (hT he) f (hT hf) hef

/-- Independence between edge classes is expressed by disjoint endpoint sets. -/
def IndependentEdgeClasses (G : LabeledMultigraph V E) (A B : Finset E) : Prop :=
  ∀ e ∈ A, ∀ f ∈ B, Disjoint (G.ends e) (G.ends f)

theorem matching_union_of_independent
    (G : LabeledMultigraph V E) {A B S T : Finset E}
    (hcross : G.IndependentEdgeClasses A B)
    (hS : (G.restrictEdges A).IsMatching S)
    (hT : (G.restrictEdges B).IsMatching T) : G.IsMatching (S ∪ T) := by
  have hs := (restrictEdges_isMatching_iff G A S).1 hS
  have ht := (restrictEdges_isMatching_iff G B T).1 hT
  refine ⟨Finset.union_subset hs.1.1 ht.1.1, ?_⟩
  intro e he f hf hef
  rcases Finset.mem_union.1 he with he | he <;>
    rcases Finset.mem_union.1 hf with hf | hf
  · exact hs.1.2 e he f hf hef
  · exact hcross e (hs.2 he) f (ht.2 hf)
  · exact (hcross f (hs.2 hf) e (ht.2 he)).symm
  · exact ht.1.2 e he f hf hef

private theorem union_inter_left_of_partition
    {A B S T : Finset E} (hAB : Disjoint A B)
    (hS : S ⊆ A) (hT : T ⊆ B) : (S ∪ T) ∩ A = S := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨heS | heT, heA⟩
    · exact heS
    · exact False.elim ((Finset.disjoint_left.1 hAB) heA (hT heT))
  · intro he
    exact ⟨Or.inl he, hS he⟩

/-- Exact matching multiplicativity for a partition into independent edge
classes. The proof uses the union/splitting bijection on labeled matchings. -/
theorem matchingCount_eq_mul_of_independent_partition
    (G : LabeledMultigraph V E) (A B : Finset E)
    (hcover : G.edges = A ∪ B) (hAB : Disjoint A B)
    (hcross : G.IndependentEdgeClasses A B) :
    G.matchingCount = (G.restrictEdges A).matchingCount *
      (G.restrictEdges B).matchingCount := by
  classical
  unfold matchingCount
  rw [← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ ↦ p.1 ∪ p.2)
  · intro p hp
    have hp' := Finset.mem_product.1 hp
    exact (mem_matchingFamily_iff G _).2 (matching_union_of_independent G hcross
      ((mem_matchingFamily_iff _ _).1 hp'.1)
      ((mem_matchingFamily_iff _ _).1 hp'.2))
  · intro p hp q hq heq
    have hp' := Finset.mem_product.1 hp
    have hq' := Finset.mem_product.1 hq
    have hpA := (restrictEdges_isMatching_iff G A p.1).1
      ((mem_matchingFamily_iff _ _).1 hp'.1) |>.2
    have hpB := (restrictEdges_isMatching_iff G B p.2).1
      ((mem_matchingFamily_iff _ _).1 hp'.2) |>.2
    have hqA := (restrictEdges_isMatching_iff G A q.1).1
      ((mem_matchingFamily_iff _ _).1 hq'.1) |>.2
    have hqB := (restrictEdges_isMatching_iff G B q.2).1
      ((mem_matchingFamily_iff _ _).1 hq'.2) |>.2
    apply Prod.ext
    · have h := congrArg (fun S ↦ S ∩ A) heq
      simpa only [union_inter_left_of_partition hAB hpA hpB,
        union_inter_left_of_partition hAB hqA hqB] using h
    · have h := congrArg (fun S ↦ S ∩ B) heq
      rw [Finset.union_comm p.1, Finset.union_comm q.1] at h
      simpa only [union_inter_left_of_partition hAB.symm hpB hpA,
        union_inter_left_of_partition hAB.symm hqB hqA] using h
  · intro S hS
    have hs := (mem_matchingFamily_iff G S).1 hS
    refine ⟨(S ∩ A, S ∩ B), ?_, ?_⟩
    · apply Finset.mem_product.2
      constructor
      · apply (mem_matchingFamily_iff _ _).2
        exact (restrictEdges_isMatching_iff G A _).2
          ⟨matching_subset G hs Finset.inter_subset_left, Finset.inter_subset_right⟩
      · apply (mem_matchingFamily_iff _ _).2
        exact (restrictEdges_isMatching_iff G B _).2
          ⟨matching_subset G hs Finset.inter_subset_left, Finset.inter_subset_right⟩
    · change (S ∩ A) ∪ (S ∩ B) = S
      rw [← Finset.inter_union_distrib_left, ← hcover]
      exact Finset.inter_eq_left.mpr hs.1

theorem matchingCount_eq_of_edges_ends
    (G H : LabeledMultigraph V E) (he : G.edges = H.edges)
    (hend : G.ends = H.ends) : G.matchingCount = H.matchingCount := by
  have hf : G.matchingFamily = H.matchingFamily := by
    ext S
    simp only [mem_matchingFamily_iff, IsMatching, toHypergraph,
      LabeledHypergraph.IsMatching, he, hend]
  exact congrArg Finset.card hf

/-- An edge disjoint from the active complement has all endpoints in D. -/
theorem ends_subset_of_disjoint_complement
    (G : LabeledMultigraph V E) (D : Finset V) {e : E}
    (he : e ∈ G.edges) (hd : Disjoint (G.ends e) (G.vertices \ D)) :
    G.ends e ⊆ D := by
  classical
  intro v hv
  by_contra hvD
  exact (Finset.disjoint_left.1 hd) hv
    (Finset.mem_sdiff.2 ⟨G.ends_subset e he hv, hvD⟩)

/-- Multiplicativity for actual vertex deletion across an empty boundary.
Isolated vertices are allowed on either side. -/
theorem matchingCount_eq_mul_of_empty_boundary
    (G : LabeledMultigraph V E) (D : Finset V)
    (hboundary : G.boundaryEdges D = ∅) :
    G.matchingCount =
      (G.deleteVertices (G.vertices \ D)).matchingCount *
        (G.deleteVertices D).matchingCount := by
  classical
  let A := (G.deleteVertices (G.vertices \ D)).edges
  let B := (G.deleteVertices D).edges
  have haSub : A ⊆ G.edges := fun _ he ↦ (mem_deleteVertices_edges_iff _ _ _).1 he |>.1
  have hbSub : B ⊆ G.edges := fun _ he ↦ (mem_deleteVertices_edges_iff _ _ _).1 he |>.1
  have hcover : G.edges = A ∪ B := by
    ext e
    constructor
    · intro he
      by_cases hD : Disjoint (G.ends e) D
      · exact Finset.mem_union_right _ ((mem_deleteVertices_edges_iff G D e).2 ⟨he, hD⟩)
      · have hc : Disjoint (G.ends e) (G.vertices \ D) := by
          by_contra hc
          have hmem := (mem_boundaryEdges_iff G D e).2 ⟨he, hD, hc⟩
          simpa [hboundary] using hmem
        exact Finset.mem_union_left _
          ((mem_deleteVertices_edges_iff G (G.vertices \ D) e).2 ⟨he, hc⟩)
    · intro he
      rcases Finset.mem_union.1 he with he | he
      · exact haSub he
      · exact hbSub he
  have hcross : G.IndependentEdgeClasses A B := by
    intro e he f hf
    have he' := (mem_deleteVertices_edges_iff G (G.vertices \ D) e).1 he
    have hf' := (mem_deleteVertices_edges_iff G D f).1 hf
    have heD := ends_subset_of_disjoint_complement G D he'.1 he'.2
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact (Finset.disjoint_left.1 hf'.2) hvf (heD hve)
  have hab : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hd := hcross e he e hf
    have hn : (G.ends e).Nonempty := Finset.card_pos.mp (by
      rw [G.ends_card e (haSub he)]
      norm_num)
    obtain ⟨v, hv⟩ := hn
    exact (Finset.disjoint_left.1 hd) hv hv
  have h := matchingCount_eq_mul_of_independent_partition G A B hcover hab hcross
  have hA : (G.restrictEdges A).matchingCount =
      (G.deleteVertices (G.vertices \ D)).matchingCount := by
    apply matchingCount_eq_of_edges_ends
    · exact Finset.inter_eq_right.mpr haSub
    · rfl
  have hB : (G.restrictEdges B).matchingCount = (G.deleteVertices D).matchingCount := by
    apply matchingCount_eq_of_edges_ends
    · exact Finset.inter_eq_right.mpr hbSub
    · rfl
  rw [hA, hB] at h
  exact h

/-- Labels supported on a set disjoint from deletion are unchanged. -/
theorem edgesOn_delete_eq (G : LabeledMultigraph V E) (D s : Finset V)
    (hs : Disjoint s D) : (G.deleteVertices D).edgesOn s = G.edgesOn s := by
  ext e
  simp only [edgesOn, Finset.mem_filter, mem_deleteVertices_edges_iff]
  change ((e ∈ G.edges ∧ Disjoint (G.ends e) D) ∧ G.ends e = s) ↔
    (e ∈ G.edges ∧ G.ends e = s)
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · rintro ⟨he, heq⟩
    exact ⟨⟨he, heq.symm ▸ hs⟩, heq⟩

theorem doubleComponent_delete_iff_of_empty_boundary
    (G : LabeledMultigraph V E) (D s : Finset V)
    (hboundary : G.boundaryEdges D = ∅) :
    (G.deleteVertices D).IsDoubleComponent s ↔
      G.IsDoubleComponent s ∧ Disjoint s D := by
  classical
  constructor
  · intro hs
    have hsSub : s ⊆ G.vertices \ D := hs.2.1.1
    have hsD : Disjoint s D := by
      rw [Finset.disjoint_left]
      intro v hv hvD
      exact (Finset.mem_sdiff.1 (hsSub hv)).2 hvD
    refine ⟨⟨hs.1, ⟨?_, ?_⟩, ?_⟩, hsD⟩
    · exact fun v hv ↦ (Finset.mem_sdiff.1 (hsSub hv)).1
    · intro e he hes
      have heD : Disjoint (G.ends e) D := by
        by_contra heD
        have hout : ¬Disjoint (G.ends e) (G.vertices \ D) := by
          obtain ⟨v, hve, hvs⟩ := Finset.not_disjoint_iff.mp hes
          exact Finset.not_disjoint_iff.mpr ⟨v, hve, hsSub hvs⟩
        have hb := (mem_boundaryEdges_iff G D e).2 ⟨he, heD, hout⟩
        simpa [hboundary] using hb
      exact hs.2.1.2 e ((mem_deleteVertices_edges_iff G D e).2 ⟨he, heD⟩) hes
    · rw [← edgesOn_delete_eq G D s hsD]
      exact hs.2.2
  · rintro ⟨hs, hsD⟩
    refine ⟨hs.1, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      exact Finset.mem_sdiff.2 ⟨hs.2.1.1 hv,
        fun hvD ↦ (Finset.disjoint_left.1 hsD) hv hvD⟩
    · intro e he hes
      exact hs.2.1.2 e ((mem_deleteVertices_edges_iff G D e).1 he).1 hes
    · rw [edgesOn_delete_eq G D s hsD]
      exact hs.2.2

theorem doubleComponents_delete_eq_filter
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅) :
    (G.deleteVertices D).doubleComponents =
      G.doubleComponents.filter (fun s ↦ Disjoint s D) := by
  ext s
  simp only [mem_doubleComponents_iff, Finset.mem_filter,
    doubleComponent_delete_iff_of_empty_boundary G D s hb]
  constructor
  · rintro ⟨hsub, hs, hd⟩
    exact ⟨⟨hs.2.1.1, hs⟩, hd⟩
  · rintro ⟨⟨hsub, hs⟩, hd⟩
    refine ⟨?_, hs, hd⟩
    intro v hv
    exact Finset.mem_sdiff.2 ⟨hsub hv, fun hvD ↦
      (Finset.disjoint_left.1 hd) hv hvD⟩

theorem empty_boundary_complement
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅) : G.boundaryEdges (G.vertices \ D) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' := (mem_boundaryEdges_iff _ _ _).1 he
  have hd : ¬Disjoint (G.ends e) D := by
    obtain ⟨v, hve, hv⟩ := Finset.not_disjoint_iff.mp he'.2.2
    have hv' := Finset.mem_sdiff.1 hv
    have hvD : v ∈ D := by
      by_contra hnot
      exact hv'.2 (Finset.mem_sdiff.2 ⟨hv'.1, hnot⟩)
    exact Finset.not_disjoint_iff.mpr ⟨v, hve, hvD⟩
  have hbad := (mem_boundaryEdges_iff G D e).2 ⟨he'.1, hd, he'.2.1⟩
  simpa [hb] using hbad

theorem doubleComponent_disjoint_complement_iff
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅) {s : Finset V} (hs : G.IsDoubleComponent s) :
    Disjoint s (G.vertices \ D) ↔ ¬Disjoint s D := by
  classical
  have hn : s.Nonempty := Finset.card_pos.mp (by rw [hs.1]; norm_num)
  constructor
  · intro hc hd
    obtain ⟨v, hv⟩ := hn
    have hvNotD := fun hvD ↦ (Finset.disjoint_left.1 hd) hv hvD
    exact (Finset.disjoint_left.1 hc) hv
      (Finset.mem_sdiff.2 ⟨hs.2.1.1 hv, hvNotD⟩)
  · intro hd
    by_contra hc
    have hne : (G.edgesOn s).Nonempty := Finset.card_pos.mp (by rw [hs.2.2]; norm_num)
    obtain ⟨e, he⟩ := hne
    have he' : e ∈ G.edges ∧ G.ends e = s := Finset.mem_filter.1 he
    have hbad : e ∈ G.boundaryEdges D := by
      apply (mem_boundaryEdges_iff G D e).2
      simpa only [he'.2] using And.intro he'.1 (And.intro hd hc)
    simpa [hb] using hbad

/-- The exceptional-component correction is additive across a cut with no
crossing edges. No new double components are introduced by such a split. -/
theorem doubleComponentCount_add_of_empty_boundary
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅) :
    (G.deleteVertices D).doubleComponentCount +
      (G.deleteVertices (G.vertices \ D)).doubleComponentCount =
        G.doubleComponentCount := by
  classical
  unfold doubleComponentCount
  rw [doubleComponents_delete_eq_filter G D hb,
    doubleComponents_delete_eq_filter G (G.vertices \ D) (empty_boundary_complement G D hb)]
  have heq : G.doubleComponents.filter (fun s ↦ Disjoint s (G.vertices \ D)) =
      G.doubleComponents.filter (fun s ↦ ¬Disjoint s D) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hd⟩
      exact ⟨hs, (doubleComponent_disjoint_complement_iff G D hb
        ((mem_doubleComponents_iff G s).1 hs).2).1 hd⟩
    · rintro ⟨hs, hd⟩
      exact ⟨hs, (doubleComponent_disjoint_complement_iff G D hb
        ((mem_doubleComponents_iff G s).1 hs).2).2 hd⟩
  rw [heq]
  exact Finset.card_filter_add_card_filter_not _

theorem vertexCount_add_of_partition
    (G : LabeledMultigraph V E) (D : Finset V) :
    (G.deleteVertices D).vertexCount +
      (G.deleteVertices (G.vertices \ D)).vertexCount = G.vertexCount := by
  have heq : G.vertices \ (G.vertices \ D) = G.vertices ∩ D := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  change (G.vertices \ D).card + (G.vertices \ (G.vertices \ D)).card = G.vertices.card
  rw [heq]
  exact Finset.card_sdiff_add_card_inter _ _

theorem edgeCount_add_of_empty_boundary
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅) :
    (G.deleteVertices D).edgeCount +
      (G.deleteVertices (G.vertices \ D)).edgeCount = G.edgeCount := by
  classical
  have heq : (G.deleteVertices (G.vertices \ D)).edges = G.crossingDeletedEdges D := by
    ext e
    simp only [mem_deleteVertices_edges_iff, mem_crossingDeletedEdges_iff]
    constructor
    · rintro ⟨he, hc⟩
      refine ⟨he, ?_⟩
      intro hd
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (G.ends e).card by
        rw [G.ends_card e he]; norm_num)
      exact (Finset.disjoint_left.1 hd) hv
        (ends_subset_of_disjoint_complement G D he hc hv)
    · rintro ⟨he, hd⟩
      refine ⟨he, ?_⟩
      by_contra hc
      have hbad := (mem_boundaryEdges_iff G D e).2 ⟨he, hd, hc⟩
      simpa [hb] using hbad
  have h := edgeCount_delete_add_crossingDeletedEdges_card G D
  simpa only [edgeCount, ← heq] using h

/-- The disconnected induction step for the full corrected inequality. -/
theorem sharpBound_of_empty_boundary
    (G : LabeledMultigraph V E) (D : Finset V)
    (hb : G.boundaryEdges D = ∅)
    (hleft : (G.deleteVertices D).SharpBound)
    (hright : (G.deleteVertices (G.vertices \ D)).SharpBound) : G.SharpBound := by
  have hv := vertexCount_add_of_partition G D
  have he := edgeCount_add_of_empty_boundary G D hb
  have hq := doubleComponentCount_add_of_empty_boundary G D hb
  have hz := matchingCount_eq_mul_of_empty_boundary G D hb
  rw [Nat.mul_comm] at hz
  unfold SharpBound at hleft hright ⊢
  have hp := Nat.mul_le_mul hleft hright
  rw [← hv, ← he, ← hq, hz]
  simp only [pow_add, mul_pow]
  convert hp using 1 <;> ring

end StableMatchingsE2E.LabeledMultigraph
