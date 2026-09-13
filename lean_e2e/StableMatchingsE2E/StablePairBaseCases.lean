import StableMatchingsE2E.StablePairComponents

namespace StableMatchingsE2E.LabeledMultigraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem matchingCount_eq_one_of_edges_empty
    (G : LabeledMultigraph V E) (he : G.edges = ∅) : G.matchingCount = 1 := by
  have hf : G.matchingFamily = {∅} := by
    ext S
    rw [mem_matchingFamily_iff, Finset.mem_singleton]
    constructor
    · intro hs
      exact Finset.subset_empty.mp (he ▸ hs.1)
    · rintro rfl
      refine ⟨Finset.empty_subset _, ?_⟩
      intro e he
      simp at he
  simp [matchingCount, hf]

theorem doubleComponentCount_eq_zero_of_edges_empty
    (G : LabeledMultigraph V E) (he : G.edges = ∅) : G.doubleComponentCount = 0 := by
  unfold doubleComponentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hcard := ((mem_doubleComponents_iff G s).1 hs).2.2.2
  simp [edgesOn, he] at hcard

theorem sharpBound_of_edges_empty
    (G : LabeledMultigraph V E) (he : G.edges = ∅) : G.SharpBound := by
  unfold SharpBound
  rw [matchingCount_eq_one_of_edges_empty G he,
    doubleComponentCount_eq_zero_of_edges_empty G he]
  simp only [pow_zero, one_mul, one_pow, mul_one]
  exact Nat.one_le_pow _ _ (by decide)

theorem edges_empty_of_vertexCount_lt_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount < 2) : G.edges = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hle := Finset.card_le_card (G.ends_subset e he)
  rw [G.ends_card e he] at hle
  change 2 ≤ G.vertexCount at hle
  omega

theorem sharpBound_of_vertexCount_lt_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount < 2) : G.SharpBound :=
  sharpBound_of_edges_empty G (edges_empty_of_vertexCount_lt_two G hv)

theorem ends_eq_vertices_of_vertexCount_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount = 2)
    {e : E} (he : e ∈ G.edges) : G.ends e = G.vertices := by
  apply Finset.eq_of_subset_of_card_le (G.ends_subset e he)
  rw [G.ends_card e he]
  exact hv.le

theorem matchingCount_eq_edgeCount_add_one_of_vertexCount_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount = 2) :
    G.matchingCount = G.edgeCount + 1 := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < G.vertices.card by rw [show G.vertices.card = 2 from hv]; norm_num)
  have hinc : G.incidentEdges x = G.edges := by
    ext e
    simp only [mem_incidentEdges_iff]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, (ends_eq_vertices_of_vertexCount_two G hv he).symm ▸ hx⟩
  have hdelSize := vertexCount_delete_singleton_add_one G hx
  have hdel := matchingCount_eq_one_of_edges_empty (G.deleteVertices {x})
    (edges_empty_of_vertexCount_lt_two _ (by omega))
  have hterms : ∀ e ∈ G.edges,
      (G.deleteVertices (G.ends e)).matchingCount = 1 := by
    intro e he
    apply matchingCount_eq_one_of_edges_empty
    apply edges_empty_of_vertexCount_lt_two
    rw [ends_eq_vertices_of_vertexCount_two G hv he]
    simp [vertexCount, deleteVertices]
  rw [matchingCount_recurrence G hx, hdel, hinc]
  simp only [Finset.sum_congr rfl hterms, Finset.sum_const, smul_eq_mul, mul_one]
  change 1 + G.edgeCount = G.edgeCount + 1
  omega

theorem doubleComponentCount_of_vertexCount_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount = 2) :
    G.doubleComponentCount = if G.edgeCount = 2 then 1 else 0 := by
  classical
  have hOn : G.edgesOn G.vertices = G.edges := by
    ext e
    simp only [edgesOn, Finset.mem_filter]
    exact ⟨And.left, fun he ↦ ⟨he, ends_eq_vertices_of_vertexCount_two G hv he⟩⟩
  have hiso : G.IsIsolatedSupport G.vertices :=
    ⟨Finset.Subset.refl _, fun e he _ ↦ ends_eq_vertices_of_vertexCount_two G hv he⟩
  have hmem : ∀ s, s ∈ G.doubleComponents ↔ s = G.vertices ∧ G.edgeCount = 2 := by
    intro s
    rw [mem_doubleComponents_iff]
    constructor
    · rintro ⟨hsub, hs⟩
      have heq : s = G.vertices := Finset.eq_of_subset_of_card_le hsub (by
        rw [hs.1]; exact hv.le)
      subst s
      exact ⟨rfl, by simpa [hOn, edgeCount] using hs.2.2⟩
    · rintro ⟨rfl, he⟩
      exact ⟨Finset.Subset.refl _, hv, hiso, by simpa [hOn, edgeCount] using he⟩
  by_cases he : G.edgeCount = 2
  · have hf : G.doubleComponents = {G.vertices} := by
      ext s
      simp [hmem, he]
    simp [doubleComponentCount, hf, he]
  · have hf : G.doubleComponents = ∅ := by
      ext s
      simp [hmem, he]
    simp [doubleComponentCount, hf, he]

theorem fourth_power_growth (k : Nat) (hk : 3 ≤ k) :
    (k + 2)^4 < 4 * (k + 1)^4 := by
  have hlin : 4 * (k + 2) ≤ 5 * (k + 1) := by omega
  have hp := Nat.pow_le_pow_left hlin 4
  simp only [mul_pow] at hp
  norm_num at hp
  have hpos : 0 < (k + 1)^4 := by positivity
  omega

theorem two_vertex_uncorrected_arithmetic (k : Nat) (hk : 3 ≤ k) :
    (k + 1)^4 ≤ 2^(2 + 2*k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep := fourth_power_growth k hk
    have hi := Nat.mul_le_mul_left 4 ih
    have hexp : 2 + 2 * (k + 1) = (2 + 2*k) + 2 := by omega
    rw [hexp, pow_add]
    norm_num
    rw [show k + 1 + 1 = k + 2 by omega]
    omega

theorem sharpBound_of_vertexCount_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount = 2) : G.SharpBound := by
  unfold SharpBound
  rw [matchingCount_eq_edgeCount_add_one_of_vertexCount_two G hv,
    doubleComponentCount_of_vertexCount_two G hv, hv]
  by_cases he : G.edgeCount = 2
  · simp [he]
  · simp only [if_neg he, pow_zero, one_mul, mul_one]
    by_cases hsmall : G.edgeCount < 3
    · interval_cases h : G.edgeCount <;> norm_num [h] at *
    · exact two_vertex_uncorrected_arithmetic _ (by omega)

theorem sharpBound_of_vertexCount_le_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount ≤ 2) : G.SharpBound := by
  rcases lt_or_eq_of_le hv with h | h
  · exact sharpBound_of_vertexCount_lt_two G h
  · exact sharpBound_of_vertexCount_two G h

end StableMatchingsE2E.LabeledMultigraph
