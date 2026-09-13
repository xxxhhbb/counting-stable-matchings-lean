import StableMatchingsE2E.StablePairMatchedCoefficients

namespace StableMatchingsE2E.LabeledMultigraph
open StablePairCoefficients
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem normalized_unique_neighbor_recurrence
    (G : LabeledMultigraph V E) {x y : V} (hx : x ∈ G.vertices)
    (hu : ∀ e ∈ G.incidentEdges x, G.ends e = {x,y}) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) =
      ((G.deleteVertices {x}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) +
      (G.degree x:ℝ)*(((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount)) := by
  rw [normalized_matching_recurrence G hx]
  congr 1
  calc (∑ e ∈ G.incidentEdges x,
      ((G.deleteVertices (G.ends e)).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount)) =
      ∑ _e ∈ G.incidentEdges x,
        ((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hu e he]
       _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, degree]

theorem normalized_singleton_bound_of_q_le_one
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices)
    (hH : (G.deleteVertices {x}).SharpBound)
    (hq : (G.deleteVertices {x}).doubleComponentCount ≤ 1) :
    ((G.deleteVertices {x}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      t^(1+2*G.degree x)*gamma := by
  have ht := t_pos
  have h := normalized_delete_singleton_bound G hx hH
  have hp : gamma^(G.deleteVertices {x}).doubleComponentCount ≤ gamma := by
    simpa only [pow_one] using pow_le_pow_right₀ gamma_gt_one.le hq
  exact h.trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- The full degree-one connected induction branch. -/
theorem normalized_strict_connected_degree_one
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : G.degree x = 1)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  obtain ⟨y, hy, hxy, ha, hu⟩ := exists_unique_neighbor_of_degree_one G hd
  have hD := degree_lt_unique_neighbor_of_cutConnected G hc hv hx hy hxy hu
  have hs1 := vertexCount_delete_singleton_add_one G hx
  have hs2 := vertexCount_delete_pair_add_two G hx hy hxy
  have hH1 := ih (G.deleteVertices {x}) (by omega)
  have hH2 := ih (G.deleteVertices {x,y}) (by omega)
  have hr := normalized_unique_neighbor_recurrence G hx hu
  rw [hd] at hr
  norm_num only [Nat.cast_one, one_mul] at hr
  have hp := normalized_pairCoeff_bound G hc hx hy hxy hH2
  rw [hd, ha] at hp
  have htotal : (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
    by_cases hdy : G.degree y = 2
    · have hq := doubleComponentCount_delete_eq_zero_of_unique_degree_two_neighbor G hc hx hu hdy ha
      have hU := normalized_delete_singleton_bound G hx hH1
      rw [hd, hq] at hU
      norm_num only [Nat.reduceAdd, Nat.reduceMul, pow_zero, mul_one] at hU
      have hP : pairCoeff 1 2 1 = (3/8:ℝ) := by
        rw [pairCoeff_eq 1 2 1 (by omega) (by omega)]
        norm_num
        rw [t_fourth]
        norm_num
      rw [hdy, hP] at hp
      rw [hr]
      exact (add_le_add hU hp).trans_lt low_degree_one_two
    · have hq := doubleComponentCount_delete_le_one_of_unique_neighbor G hc hx hu
      have hU := normalized_singleton_bound_of_q_le_one G hx hH1 hq
      rw [hd] at hU
      norm_num only [Nat.reduceAdd, Nat.reduceMul] at hU
      have hP := pairCoeff_antitone_degree 1 1 3 (G.degree y) (by omega) (by omega) (by omega)
      have heval : pairCoeff 1 3 1 = (9/32:ℝ) := by
        rw [pairCoeff_eq 1 3 1 (by omega) (by omega)]
        norm_num
        rw [t_fourth]
        norm_num
      rw [heval] at hP
      rw [hr]
      exact (add_le_add hU (hp.trans hP)).trans_lt low_degree_one_large
  exact htotal

theorem sharpBound_connected_degree_one
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : G.degree x = 1)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    G.SharpBound := by
  apply (sharpBound_iff_normalized G).mpr
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero]
  exact (normalized_strict_connected_degree_one G hc hv hx hd ih).le

/-- Degree two with one neighbor and two parallel labels. -/
theorem normalized_strict_connected_degree_two_unique
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hd : G.degree x = 2) (ha : G.multiplicity x y = 2)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  have hu := unique_neighbor_of_multiplicity_eq_degree G hxy (ha.trans hd.symm)
  have hD := degree_lt_unique_neighbor_of_cutConnected G hc hv hx hy hxy hu
  have hs1 := vertexCount_delete_singleton_add_one G hx
  have hs2 := vertexCount_delete_pair_add_two G hx hy hxy
  have hH1 := ih (G.deleteVertices {x}) (by omega)
  have hH2 := ih (G.deleteVertices {x,y}) (by omega)
  have hq := doubleComponentCount_delete_le_one_of_unique_neighbor G hc hx hu
  have hU := normalized_singleton_bound_of_q_le_one G hx hH1 hq
  rw [hd] at hU
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hU
  have hp := normalized_pairCoeff_bound G hc hx hy hxy hH2
  rw [hd, ha] at hp
  have hP := pairCoeff_antitone_degree 2 2 3 (G.degree y) (by omega) (by omega) (by omega)
  have heval : (2:ℝ)*pairCoeff 2 3 2 = gamma/2 := by
    rw [pairCoeff_eq 2 3 2 (by omega) (by omega)]
    norm_num
    have h6 : t^6 = t^2/2 := by
      calc t^6 = t^2*t^4 := by ring
           _ = t^2/2 := by rw [t_fourth]; ring
    rw [h6]
    unfold gamma
    ring
  have hp2 := mul_le_mul_of_nonneg_left (hp.trans hP) (by norm_num : (0:ℝ) ≤ 2)
  rw [heval] at hp2
  have hr := normalized_unique_neighbor_recurrence G hx hu
  rw [hd] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have htotal : (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
    rw [hr]
    exact (add_le_add hU hp2).trans_lt low_degree_two_unique
  exact htotal

theorem sharpBound_connected_degree_two_unique
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hd : G.degree x = 2) (ha : G.multiplicity x y = 2)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    G.SharpBound := by
  apply (sharpBound_iff_normalized G).mpr
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero]
  exact (normalized_strict_connected_degree_two_unique G hc hv hx hy hxy hd ha ih).le

end StableMatchingsE2E.LabeledMultigraph
