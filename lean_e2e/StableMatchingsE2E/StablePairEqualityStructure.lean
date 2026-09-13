import StableMatchingsE2E.StablePairEquality

namespace StableMatchingsE2E.LabeledMultigraph
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

def IsSmallPairComponent (G : LabeledMultigraph V E) (s : Finset V) : Prop :=
  s.card = 2 ∧ G.IsIsolatedSupport s ∧ 1 ≤ (G.edgesOn s).card ∧ (G.edgesOn s).card ≤ 3

theorem isolatedSupport_lift_of_empty_boundary
    (G : LabeledMultigraph V E) (D s : Finset V) (hb : G.boundaryEdges D = ∅)
    (hs : (G.deleteVertices D).IsIsolatedSupport s) :
    G.IsIsolatedSupport s ∧ Disjoint s D := by
  classical
  have hsub : s ⊆ G.vertices \ D := hs.1
  have hd : Disjoint s D := by
    apply Finset.disjoint_left.mpr
    intro x hx hxD
    exact (Finset.mem_sdiff.mp (hsub hx)).2 hxD
  refine ⟨⟨fun x hx ↦ (Finset.mem_sdiff.mp (hsub hx)).1,?_⟩,hd⟩
  intro e he hmeet
  have heD : Disjoint (G.ends e) D := by
    by_contra hn
    obtain ⟨x,hxe,hxs⟩ := Finset.not_disjoint_iff.mp hmeet
    have hout : ¬Disjoint (G.ends e) (G.vertices \ D) :=
      Finset.not_disjoint_iff.mpr ⟨x,hxe,hsub hxs⟩
    have hbad := (mem_boundaryEdges_iff G D e).mpr ⟨he,hn,hout⟩
    simpa [hb] using hbad
  exact hs.2 e ((mem_deleteVertices_edges_iff G D e).mpr ⟨he,heD⟩) hmeet

theorem smallPairComponent_lift_of_empty_boundary
    (G : LabeledMultigraph V E) (D s : Finset V) (hb : G.boundaryEdges D = ∅)
    (hs : (G.deleteVertices D).IsSmallPairComponent s) : G.IsSmallPairComponent s := by
  have hl := isolatedSupport_lift_of_empty_boundary G D s hb hs.2.1
  refine ⟨hs.1,hl.1,?_⟩
  rw [← edgesOn_delete_eq G D s hl.2]
  exact hs.2.2

theorem exists_smallPairComponent_of_decomposition
    {G : LabeledMultigraph V E} (h : G.PairComponentDecomposition) :
    ∀ x ∈ G.vertices, ∃ s : Finset V, x ∈ s ∧ G.IsSmallPairComponent s := by
  induction h with
  | empty H hv =>
    intro x hx
    have hpos : 0 < H.vertexCount := Finset.card_pos.mpr ⟨x,hx⟩
    omega
  | pair H hv he =>
    intro x hx
    have hOn : H.edgesOn H.vertices = H.edges := by
      ext e
      simp only [edgesOn,Finset.mem_filter]
      exact ⟨And.left,fun he ↦ ⟨he,ends_eq_vertices_of_vertexCount_two H hv he⟩⟩
    refine ⟨H.vertices,hx,hv,⟨Finset.Subset.refl _,?_⟩,?_⟩
    · intro e he hm
      exact ends_eq_vertices_of_vertexCount_two H hv he
    · rw [hOn]
      change 1 ≤ H.edgeCount ∧ H.edgeCount ≤ 3
      omega
  | split H D hsub hn hn' hb left right ihl ihr =>
    intro x hx
    by_cases hxD : x ∈ D
    · have hxR : x ∈ (H.deleteVertices (H.vertices \ D)).vertices :=
        Finset.mem_sdiff.mpr ⟨hx,fun h ↦ (Finset.mem_sdiff.mp h).2 hxD⟩
      obtain ⟨s,hxs,hs⟩ := ihr x hxR
      exact ⟨s,hxs,smallPairComponent_lift_of_empty_boundary H _ s (empty_boundary_complement H D hb) hs⟩
    · obtain ⟨s,hxs,hs⟩ := ihl x (Finset.mem_sdiff.mpr ⟨hx,hxD⟩)
      exact ⟨s,hxs,smallPairComponent_lift_of_empty_boundary H D s hb hs⟩

/-- Equality and exclusion of isolated parallel pairs force a genuine matching
cover of the entire vertex set, not just an abstract decomposition certificate. -/
theorem unique_incident_edge_of_sharpEquality
    (G : LabeledMultigraph V E) (heq : G.SharpEquality)
    (hno : ∀ s : Finset V, s.card = 2 → G.IsIsolatedSupport s → (G.edgesOn s).card ≤ 1) :
    ∀ x ∈ G.vertices, ∃ e ∈ G.edges, x ∈ G.ends e ∧
      ∀ f ∈ G.edges, x ∈ G.ends f → f=e := by
  intro x hx
  obtain ⟨s,hxs,hs⟩ := exists_smallPairComponent_of_decomposition
    ((sharpEquality_iff_pairComponentDecomposition G).mp heq) x hx
  have hle := hno s hs.1 hs.2.1
  obtain ⟨e,he⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hs.2.2.1)
  have he' : e ∈ G.edges ∧ G.ends e=s := Finset.mem_filter.mp he
  refine ⟨e,he'.1,he'.2.symm ▸ hxs,?_⟩
  intro f hf hxf
  have hfs := hs.2.1.2 f hf (Finset.not_disjoint_iff.mpr ⟨x,hxf,hxs⟩)
  exact Finset.card_le_one.mp hle f (Finset.mem_filter.mpr ⟨hf,hfs⟩) e he

end StableMatchingsE2E.LabeledMultigraph
