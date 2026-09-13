import StableMatchingsE2E.StablePairBaseCases

namespace StableMatchingsE2E.LabeledMultigraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem degree_pos_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    (hv : 2 ≤ G.vertexCount) {x : V} (hx : x ∈ G.vertices) :
    0 < G.degree x := by
  have hnon : (G.vertices \ {x}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (by simpa using hx),
      Finset.card_singleton]
    change 0 < G.vertexCount - 1
    omega
  obtain ⟨e, he, hex, _⟩ := hc {x} (by simpa using hx) (by simp) hnon
  have hxe : x ∈ G.ends e := by
    simpa only [Finset.disjoint_singleton_right, not_not] using hex
  exact Finset.card_pos.mpr ⟨e, (mem_incidentEdges_iff G x e).2 ⟨he, hxe⟩⟩

/-- In a connected graph with at least three vertices, a unique neighbor
of x has an edge leaving the two-vertex set. -/
theorem exists_extra_edge_at_unique_neighbor
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    (hv : 3 ≤ G.vertexCount) {x y : V}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hu : ∀ e ∈ G.incidentEdges x, G.ends e = {x, y}) :
    ∃ e ∈ G.incidentEdges y, e ∉ G.incidentEdges x := by
  classical
  have hsub : ({x, y} : Finset V) ⊆ G.vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx, hy⟩
  have hn : (G.vertices \ {x, y}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]
    have hpair : ({x, y} : Finset V).card = 2 := by simp [hxy]
    rw [hpair]
    change 0 < G.vertexCount - 2
    omega
  obtain ⟨e, he, hin, hout⟩ := hc {x, y} hsub (by simp) hn
  have hnotx : x ∉ G.ends e := by
    intro hxe
    have heq := hu e ((mem_incidentEdges_iff G x e).2 ⟨he, hxe⟩)
    rw [heq, Finset.not_disjoint_iff] at hout
    obtain ⟨v, hvp, hvo⟩ := hout
    exact (Finset.mem_sdiff.1 hvo).2 hvp
  obtain ⟨v, hve, hvp⟩ := Finset.not_disjoint_iff.mp hin
  have hcases : v = x ∨ v = y := by simpa using hvp
  have hye : y ∈ G.ends e := by
    rcases hcases with h | h
    · exact False.elim (hnotx (h ▸ hve))
    · exact h ▸ hve
  refine ⟨e, (mem_incidentEdges_iff G y e).2 ⟨he, hye⟩, ?_⟩
  exact fun hex ↦ hnotx ((mem_incidentEdges_iff G x e).1 hex).2

theorem degree_lt_unique_neighbor_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    (hv : 3 ≤ G.vertexCount) {x y : V}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hu : ∀ e ∈ G.incidentEdges x, G.ends e = {x, y}) :
    G.degree x < G.degree y := by
  have hsub : G.incidentEdges x ⊆ G.incidentEdges y := by
    intro e he
    have he' := (mem_incidentEdges_iff G x e).1 he
    exact (mem_incidentEdges_iff G y e).2 ⟨he'.1, by rw [hu e he]; simp⟩
  obtain ⟨e, hey, hex⟩ := exists_extra_edge_at_unique_neighbor G hc hv hx hy hxy hu
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq ↦ hex (heq.symm ▸ hey)⟩

theorem exists_positive_min_degree_vertex
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    (hv : 2 ≤ G.vertexCount) :
    ∃ x ∈ G.vertices, 0 < G.degree x ∧ ∀ y ∈ G.vertices, G.degree x ≤ G.degree y := by
  have hn : G.vertices.Nonempty := Finset.card_pos.mp (show 0 < G.vertexCount by omega)
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image G.vertices G.degree hn
  exact ⟨x, hx, degree_pos_of_cutConnected G hc hv hx, hmin⟩

/-- Failure of cut-connectedness supplies a proper empty-boundary split. -/
theorem exists_split_of_not_cutConnected
    (G : LabeledMultigraph V E) (hc : ¬G.CutConnected) :
    ∃ D : Finset V, D ⊆ G.vertices ∧ D.Nonempty ∧ (G.vertices \ D).Nonempty ∧
      G.boundaryEdges D = ∅ := by
  classical
  unfold CutConnected at hc
  push_neg at hc
  obtain ⟨D, hsub, hn, hn', hcut⟩ := hc
  refine ⟨D, hsub, hn, hn', ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' := (mem_boundaryEdges_iff G D e).1 he
  exact he'.2.2 (hcut e he'.1 he'.2.1)

/-- Strong-induction assembly. The connected large-graph step remains an
explicit hypothesis; this theorem does not claim that step has been proved. -/
theorem sharpBound_from_connected_step
    (hstep : ∀ G : LabeledMultigraph V E, G.CutConnected → 3 ≤ G.vertexCount →
      (∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) →
      G.SharpBound) (G : LabeledMultigraph V E) : G.SharpBound := by
  classical
  have hall : ∀ n, ∀ H : LabeledMultigraph V E, H.vertexCount = n → H.SharpBound := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hn
      by_cases hsmall : H.vertexCount ≤ 2
      · exact sharpBound_of_vertexCount_le_two H hsmall
      have hlarge : 3 ≤ H.vertexCount := by omega
      have hsmaller : ∀ J : LabeledMultigraph V E,
          J.vertexCount < H.vertexCount → J.SharpBound := by
        intro J hJ
        exact ih J.vertexCount (by omega) J rfl
      by_cases hc : H.CutConnected
      · exact hstep H hc hlarge hsmaller
      obtain ⟨D, hsub, hD, hcomp, hb⟩ := exists_split_of_not_cutConnected H hc
      have hsum := vertexCount_add_of_partition H D
      have hleft : 0 < (H.deleteVertices D).vertexCount := Finset.card_pos.mpr hcomp
      have hright : 0 < (H.deleteVertices (H.vertices \ D)).vertexCount := by
        apply Finset.card_pos.mpr
        obtain ⟨v, hv⟩ := hD
        refine ⟨v, Finset.mem_sdiff.mpr ⟨hsub hv, ?_⟩⟩
        exact fun h ↦ (Finset.mem_sdiff.mp h).2 hv
      exact sharpBound_of_empty_boundary H D hb
        (hsmaller _ (by omega)) (hsmaller _ (by omega))
  exact hall G.vertexCount G rfl

end StableMatchingsE2E.LabeledMultigraph
