import StableMatchingsE2E.StablePairLowDegree

namespace StableMatchingsE2E.LabeledMultigraph
open StablePairCoefficients
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem eligibleNeighbors_subset_pair
    (G : LabeledMultigraph V E) {x y z : V} {e f : E}
    (hi : G.incidentEdges x = {e,f}) (he : G.ends e = {x,y}) (hf : G.ends f = {x,z}) :
    G.eligibleNeighbors x ⊆ ({y,z} : Finset V).filter (fun w ↦ 3 ≤ G.degree w) := by
  classical
  intro w hw
  have hw' : w ∈ G.vertices ∧ w ≠ x ∧ 0 < G.multiplicity x w ∧ 3 ≤ G.degree w :=
    Finset.mem_filter.mp hw
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hw'.2.2.1
  have ha' := (mem_edgesBetween_iff G x w a).mp ha
  have hai := (mem_incidentEdges_iff G x a).mpr ⟨ha'.1, ha'.2.1⟩
  have hac : a = e ∨ a = f := by simpa [hi] using hai
  have hwPair : w ∈ ({y,z} : Finset V) := by
    rcases hac with rfl | rfl
    · have h := ha'.2.2
      rw [he] at h
      have hwy : w = y := by simpa [hw'.2.1] using h
      simp [hwy]
    · have h := ha'.2.2
      rw [hf] at h
      have hwz : w = z := by simpa [hw'.2.1] using h
      simp [hwz]
  exact Finset.mem_filter.mpr ⟨hwPair, hw'.2.2.2⟩

theorem normalized_degree_two_simple_pair_bound
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hd : G.degree x = 2) (hdy : 2 ≤ G.degree y) (ha : G.multiplicity x y = 1)
    (hH : (G.deleteVertices {x,y}).SharpBound) :
    ((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      if G.degree y = 2 then (9/32:ℝ) else 27/128 := by
  have h := normalized_pairCoeff_bound G hc hx hy hxy hH
  rw [hd, ha] at h
  by_cases hy2 : G.degree y = 2
  · rw [if_pos hy2]
    rw [hy2] at h
    have hv : pairCoeff 2 2 1 = (9/32:ℝ) := by
      rw [pairCoeff_eq 2 2 1 (by omega) (by omega)]
      norm_num
      rw [t_fourth]
      norm_num
    simpa only [hv] using h
  · rw [if_neg hy2]
    have hp := pairCoeff_antitone_degree 2 1 3 (G.degree y) (by omega) (by omega) (by omega)
    have hv : pairCoeff 2 3 1 = (27/128:ℝ) := by
      rw [pairCoeff_eq 2 3 1 (by omega) (by omega)]
      norm_num
      rw [t_fourth]
      norm_num
    rw [hv] at hp
    exact h.trans hp

theorem normalized_strict_connected_degree_two_distinct
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x y z : V} {e f : E}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hz : z ∈ G.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hef : e ≠ f)
    (hi : G.incidentEdges x = {e,f}) (he : G.ends e = {x,y}) (hf : G.ends f = {x,z})
    (hd : G.degree x = 2) (hdy : 2 ≤ G.degree y) (hdz : 2 ≤ G.degree z)
    (hay : G.multiplicity x y = 1) (haz : G.multiplicity x z = 1)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  classical
  have ht := t_pos
  have hs1 := vertexCount_delete_singleton_add_one G hx
  have hsy := vertexCount_delete_pair_add_two G hx hy hxy
  have hsz := vertexCount_delete_pair_add_two G hx hz hxz
  have hU := normalized_delete_singleton_bound G hx (ih _ (by omega))
  rw [hd] at hU
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hU
  have hq := (doubleComponentCount_delete_le_eligibleNeighbors_card G hc hx).trans
    (Finset.card_le_card (eligibleNeighbors_subset_pair G hi he hf))
  have hUp := hU.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ gamma_gt_one.le hq) (by positivity))
  have hY := normalized_degree_two_simple_pair_bound G hc hx hy hxy hd hdy hay (ih _ (by omega))
  have hZ := normalized_degree_two_simple_pair_bound G hc hx hz hxz hd hdz haz (ih _ (by omega))
  have hr := normalized_matching_recurrence G hx
  rw [hi, Finset.sum_pair hef, he, hf] at hr
  have htotal : (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
    by_cases hy2 : G.degree y = 2 <;> by_cases hz2 : G.degree z = 2
    · simp [Finset.filter_insert, Finset.filter_singleton, hy2, hz2] at hUp hY hZ
      have hnum := low_degree_two_no_high
      linarith
    · have hz3 : 3 ≤ G.degree z := by omega
      simp [Finset.filter_insert, Finset.filter_singleton, hy2, hz2, hz3] at hUp hY hZ
      have hnum := low_degree_two_one_high
      linarith
    · have hy3 : 3 ≤ G.degree y := by omega
      simp [Finset.filter_insert, Finset.filter_singleton, hy2, hz2, hy3] at hUp hY hZ
      have hnum := low_degree_two_one_high
      linarith
    · have hy3 : 3 ≤ G.degree y := by omega
      have hz3 : 3 ≤ G.degree z := by omega
      simp [Finset.filter_insert, Finset.filter_singleton, hy2, hz2, hy3, hz3, hyz] at hUp hY hZ
      have hnum := low_degree_two_two_high
      linarith
  exact htotal

theorem sharpBound_connected_degree_two_distinct
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x y z : V} {e f : E}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hz : z ∈ G.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hef : e ≠ f)
    (hi : G.incidentEdges x = {e,f}) (he : G.ends e = {x,y}) (hf : G.ends f = {x,z})
    (hd : G.degree x = 2) (hdy : 2 ≤ G.degree y) (hdz : 2 ≤ G.degree z)
    (hay : G.multiplicity x y = 1) (haz : G.multiplicity x z = 1)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    G.SharpBound := by
  apply (sharpBound_iff_normalized G).mpr
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero]
  exact (normalized_strict_connected_degree_two_distinct G hc hv hx hy hz hxy hxz hyz hef
    hi he hf hd hdy hdz hay haz ih).le

/-- Distinct endpoints of the two incident labels force multiplicity one. -/
theorem multiplicity_eq_one_of_two_distinct_neighbors
    (G : LabeledMultigraph V E) {x y z : V} {e f : E}
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hi : G.incidentEdges x = {e,f}) (he : G.ends e = {x,y}) (hf : G.ends f = {x,z}) :
    G.multiplicity x y = 1 := by
  classical
  have hset : G.edgesBetween x y = {e} := by
    ext a
    constructor
    · intro ha
      have ha' := (mem_edgesBetween_iff G x y a).mp ha
      have hai := (mem_incidentEdges_iff G x a).mpr ⟨ha'.1, ha'.2.1⟩
      have hac : a = e ∨ a = f := by simpa [hi] using hai
      rcases hac with rfl | rfl
      · simp
      · have h := ha'.2.2
        rw [hf] at h
        simp [Ne.symm hxy, hyz] at h
    · intro ha
      have hae : a = e := by simpa using ha
      subst a
      have hei : e ∈ G.incidentEdges x := by simp [hi]
      exact (mem_edgesBetween_iff G x y e).mpr
        ⟨((mem_incidentEdges_iff G x e).mp hei).1, by simp [he], by simp [he]⟩
  unfold multiplicity
  rw [hset]
  simp

/-- Exhaustive degree-two branch: either parallel labels or distinct neighbors. -/
theorem normalized_strict_connected_degree_two
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : G.degree x = 2)
    (hmin : ∀ y ∈ G.vertices, G.degree x ≤ G.degree y)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  classical
  obtain ⟨e, f, hef, hi⟩ := Finset.card_eq_two.mp hd
  have hei : e ∈ G.incidentEdges x := by simp [hi]
  have hfi : f ∈ G.incidentEdges x := by simp [hi]
  obtain ⟨y, hy, hxy, he⟩ := exists_other_endpoint G hei
  obtain ⟨z, hz, hxz, hf⟩ := exists_other_endpoint G hfi
  by_cases hyz : y = z
  · subst z
    have hset : G.edgesBetween x y = G.incidentEdges x := by
      ext a
      constructor
      · intro ha
        have h := (mem_edgesBetween_iff G x y a).mp ha
        exact (mem_incidentEdges_iff G x a).mpr ⟨h.1,h.2.1⟩
      · intro ha
        have h := (mem_incidentEdges_iff G x a).mp ha
        have hac : a = e ∨ a = f := by simpa [hi] using ha
        refine (mem_edgesBetween_iff G x y a).mpr ⟨h.1,h.2,?_⟩
        rcases hac with rfl | rfl <;> simp [he, hf]
    have ha : G.multiplicity x y = 2 := by
      unfold multiplicity
      rw [hset]
      exact hd
    exact normalized_strict_connected_degree_two_unique G hc hv hx hy hxy hd ha ih
  · have hay := multiplicity_eq_one_of_two_distinct_neighbors G hxy hyz hi he hf
    have hi' : G.incidentEdges x = {f,e} := by rw [hi]; exact Finset.pair_comm e f
    have haz := multiplicity_eq_one_of_two_distinct_neighbors G hxz (Ne.symm hyz) hi' hf he
    exact normalized_strict_connected_degree_two_distinct G hc hv hx hy hz hxy hxz hyz hef
      hi he hf hd (hd ▸ hmin y hy) (hd ▸ hmin z hz) hay haz ih

theorem sharpBound_connected_degree_two
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : G.degree x = 2)
    (hmin : ∀ y ∈ G.vertices, G.degree x ≤ G.degree y)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    G.SharpBound := by
  apply (sharpBound_iff_normalized G).mpr
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero]
  exact (normalized_strict_connected_degree_two G hc hv hx hd hmin ih).le

/-- Universal labeled loopless multigraph counting bound, including the exact
isolated-double-component correction. No connected-step hypothesis remains. -/
theorem sharpBound (G : LabeledMultigraph V E) : G.SharpBound := by
  apply sharpBound_from_connected_step ?_ G
  intro H hc hv ih
  obtain ⟨x,hx,hpos,hmin⟩ := exists_positive_min_degree_vertex H hc (by omega)
  by_cases h1 : H.degree x = 1
  · exact sharpBound_connected_degree_one H hc hv hx h1 ih
  by_cases h2 : H.degree x = 2
  · exact sharpBound_connected_degree_two H hc hv hx h2 hmin ih
  exact sharpBound_connected_high_degree H hc hv hx (by omega) hmin ih

/-- Every connected graph of order at least three is strictly below the bound. -/
theorem normalized_strict_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  have ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound :=
    fun H _ ↦ sharpBound H
  obtain ⟨x,hx,hpos,hmin⟩ := exists_positive_min_degree_vertex G hc (by omega)
  by_cases h1 : G.degree x = 1
  · exact normalized_strict_connected_degree_one G hc hv hx h1 ih
  by_cases h2 : G.degree x = 2
  · exact normalized_strict_connected_degree_two G hc hv hx h2 hmin ih
  exact normalized_strict_connected_high_degree G hc hv hx (by omega) hmin ih

end StableMatchingsE2E.LabeledMultigraph
