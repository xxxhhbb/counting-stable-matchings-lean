import StableMatchingsE2E.StablePairNormalization

namespace StableMatchingsE2E.StablePairCoefficients

noncomputable def pairCoeff (d D a : Nat) : ℝ :=
  t^(2+2*(d+D-a))*gamma^(d+D-2*a)

/-- Collect each boundary-edge correction together with its reciprocal
square-root factor; the combined factor is exactly 3/4. -/
theorem pairCoeff_eq (d D a : Nat) (ha : a ≤ d) (hA : a ≤ D) :
    pairCoeff d D a = t^(2+2*a)*(3/4:ℝ)^(d+D-2*a) := by
  have hn : 2+2*(d+D-a) = (2+2*a)+2*(d+D-2*a) := by omega
  unfold pairCoeff
  rw [hn, pow_add, pow_mul]
  calc t^(2+2*a)*(t^2)^(d+D-2*a)*gamma^(d+D-2*a) =
        t^(2+2*a)*(t^2*gamma)^(d+D-2*a) := by rw [mul_pow]; ring
       _ = _ := by rw [t_sq_mul_gamma]

theorem pairCoeff_antitone_degree (d a D E : Nat)
    (ha : a ≤ d) (hD : a ≤ D) (hDE : D ≤ E) :
    pairCoeff d E a ≤ pairCoeff d D a := by
  have ht := t_pos
  rw [pairCoeff_eq d E a ha (hD.trans hDE), pairCoeff_eq d D a ha hD]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

noncomputable def c : ℝ := t^2*gamma^2

theorem c_nonneg : 0 ≤ c := by unfold c; positivity

theorem c_le_one : c ≤ 1 := by
  have h2 := pow_le_pow_left₀ t_pos.le t_lt_rational.le 2
  unfold c
  rw [gamma_sq]
  norm_num at h2
  linarith

theorem c_times_t_sq : c*t^2 = (3/4:ℝ)^2 := by
  unfold c
  calc t^2*gamma^2*t^2 = (t^2*gamma)^2 := by ring
       _ = _ := by rw [t_sq_mul_gamma]

/-- On D=d, the deficit d-a gives a power of a factor at most one. -/
theorem pairCoeff_diagonal (d a : Nat) (ha : a ≤ d) :
    pairCoeff d d a = t^(2+2*d)*c^(d-a) := by
  rw [pairCoeff_eq d d a ha ha]
  have hk : d+d-2*a = 2*(d-a) := by omega
  have hn : 2+2*d = (2+2*a)+2*(d-a) := by omega
  rw [hk, pow_mul, ← c_times_t_sq, mul_pow, hn, pow_add, pow_mul]
  ring

theorem pairCoeff_high_multiple_neighbors (d D a : Nat)
    (ha : a < d) (hD : d ≤ D) :
    pairCoeff d D a ≤ t^(2*(d+2))*gamma^2 := by
  have ht := t_pos
  have hfirst := pairCoeff_antitone_degree d a d D ha.le ha.le hD
  rw [pairCoeff_diagonal d a ha.le] at hfirst
  have hpow : c^(d-a) ≤ c := by
    have h := pow_le_pow_of_le_one c_nonneg c_le_one (show 1 ≤ d-a by omega)
    simpa only [pow_one] using h
  calc pairCoeff d D a ≤ t^(2+2*d)*c^(d-a) := hfirst
       _ ≤ t^(2+2*d)*c := mul_le_mul_of_nonneg_left hpow (by positivity)
       _ = t^(2*(d+2))*gamma^2 := by
         unfold c
         rw [show 2*(d+2) = (2+2*d)+2 by omega, pow_add]
         ring

theorem pairCoeff_high_unique_neighbor (d D : Nat) (hD : d+1 ≤ D) :
    pairCoeff d D d ≤ t^(2*(d+2))*gamma^2 := by
  have ht := t_pos
  have hg := gamma_pos
  have hfirst := pairCoeff_antitone_degree d d (d+1) D le_rfl (by omega) hD
  have hid : pairCoeff d (d+1) d = t^(2*(d+2))*gamma := by
    rw [pairCoeff_eq d (d+1) d le_rfl (by omega)]
    rw [show d+(d+1)-2*d = 1 by omega, pow_one, ← t_sq_mul_gamma]
    rw [show 2*(d+2) = (2+2*d)+2 by omega, pow_add]
    ring
  rw [hid] at hfirst
  have hgg : gamma ≤ gamma^2 := by nlinarith [gamma_gt_one]
  exact hfirst.trans (mul_le_mul_of_nonneg_left hgg (by positivity))

end StableMatchingsE2E.StablePairCoefficients

namespace StableMatchingsE2E.LabeledMultigraph
open StablePairCoefficients
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem multiplicity_le_degree_left (G : LabeledMultigraph V E) (x y : V) :
    G.multiplicity x y ≤ G.degree x := by
  unfold multiplicity degree
  rw [edgesBetween_eq_inter_incidentEdges]
  exact Finset.card_le_card Finset.inter_subset_left

theorem unique_neighbor_of_multiplicity_eq_degree
    (G : LabeledMultigraph V E) {x y : V} (hxy : x ≠ y)
    (ha : G.multiplicity x y = G.degree x) :
    ∀ e ∈ G.incidentEdges x, G.ends e = {x,y} := by
  have hsub : G.edgesBetween x y ⊆ G.incidentEdges x := by
    rw [edgesBetween_eq_inter_incidentEdges]
    exact Finset.inter_subset_left
  have heq : G.edgesBetween x y = G.incidentEdges x :=
    Finset.eq_of_subset_of_card_le hsub ha.ge
  intro e he
  have he' := (mem_edgesBetween_iff G x y e).1 (heq.symm ▸ he)
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact he'.2
  · rw [G.ends_card e he'.1]
    simp [hxy]

theorem normalized_pairCoeff_bound
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hH : (G.deleteVertices {x,y}).SharpBound) :
    ((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      pairCoeff (G.degree x) (G.degree y) (G.multiplicity x y) := by
  have ht := t_pos
  have h := normalized_delete_pair_bound G hx hy hxy hH
  have hq := doubleComponentCount_delete_pair_add_twice_multiplicity_le G hc hx hy hxy
  have hq' : (G.deleteVertices {x,y}).doubleComponentCount ≤
      G.degree x+G.degree y-2*G.multiplicity x y := by omega
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ gamma_gt_one.le hq') (by positivity))

theorem normalized_pair_high_bound
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hmin : G.degree x ≤ G.degree y) (hH : (G.deleteVertices {x,y}).SharpBound) :
    ((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      t^(2*(G.degree x+2))*gamma^2 := by
  have h := normalized_pairCoeff_bound G hc hx hy hxy hH
  have ha := multiplicity_le_degree_left G x y
  rcases lt_or_eq_of_le ha with ha | ha
  · exact h.trans (pairCoeff_high_multiple_neighbors _ _ _ ha hmin)
  · have hu := unique_neighbor_of_multiplicity_eq_degree G hxy ha
    have hd := degree_lt_unique_neighbor_of_cutConnected G hc hv hx hy hxy hu
    rw [ha] at h
    exact h.trans (pairCoeff_high_unique_neighbor _ _ (by omega))

theorem exists_other_endpoint (G : LabeledMultigraph V E) {x : V} {e : E}
    (he : e ∈ G.incidentEdges x) :
    ∃ y ∈ G.vertices, x ≠ y ∧ G.ends e = {x,y} := by
  have he' := (mem_incidentEdges_iff G x e).1 he
  have hcard : ((G.ends e).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem he'.2, G.ends_card e he'.1]
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < ((G.ends e).erase x).card by omega)
  have hyE := Finset.mem_of_mem_erase hy
  have hxy := (Finset.ne_of_mem_erase hy).symm
  refine ⟨y, G.ends_subset e he'.1 hyE, hxy, ?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨he'.2, hyE⟩
  · rw [G.ends_card e he'.1]
    simp [hxy]

/-- Connected induction branch with minimum weighted degree at least three.
The only proof assumptions concern strictly smaller graphs. -/
theorem normalized_strict_connected_high_degree
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : 3 ≤ G.degree x)
    (hmin : ∀ y ∈ G.vertices, G.degree x ≤ G.degree y)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) < 1 := by
  have hsz := vertexCount_delete_singleton_add_one G hx
  have hU := normalized_unmatched_bound_of_cutConnected G hc hx (ih _ (by omega))
  have hterms : ∀ e ∈ G.incidentEdges x,
      ((G.deleteVertices (G.ends e)).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
        t^(2*(G.degree x+2))*gamma^2 := by
    intro e he
    obtain ⟨y, hy, hxy, hend⟩ := exists_other_endpoint G he
    rw [hend]
    have hsize := vertexCount_delete_pair_add_two G hx hy hxy
    exact normalized_pair_high_bound G hc hv hx hy hxy (hmin y hy) (ih _ (by omega))
  have hsum := Finset.sum_le_sum hterms
  have hsum' : (∑ e ∈ G.incidentEdges x,
      ((G.deleteVertices (G.ends e)).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount)) ≤
        (G.degree x:ℝ)*t^(2*(G.degree x+2))*gamma^2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul, degree, mul_assoc] using hsum
  have htotal : (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤ highBound (G.degree x) := by
    rw [normalized_matching_recurrence G hx]
    exact add_le_add hU hsum'
  have hstrict := htotal.trans_lt (highBound_lt _ hd)
  linarith

theorem sharpBound_connected_high_degree
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount)
    {x : V} (hx : x ∈ G.vertices) (hd : 3 ≤ G.degree x)
    (hmin : ∀ y ∈ G.vertices, G.degree x ≤ G.degree y)
    (ih : ∀ H : LabeledMultigraph V E, H.vertexCount < G.vertexCount → H.SharpBound) :
    G.SharpBound := by
  apply (sharpBound_iff_normalized G).mpr
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero]
  exact (normalized_strict_connected_high_degree G hc hv hx hd hmin ih).le

end StableMatchingsE2E.LabeledMultigraph
