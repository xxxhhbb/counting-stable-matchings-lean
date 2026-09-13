import StableMatchingsE2E.StablePairCoefficients

namespace StableMatchingsE2E.StablePairCoefficients

theorem t_power_cancel (N : Nat) : (t^N)^4 * (2:ℝ)^N = 1 := by
  rw [← pow_mul, Nat.mul_comm N 4, pow_mul, ← mul_pow, t_fourth]
  norm_num

theorem gamma_fourth : gamma^4 = (81/64 : ℝ) := by
  calc gamma^4 = (gamma^2)^2 := by ring
       _ = 81/64 := by rw [gamma_sq]; norm_num

theorem gamma_power_cancel (q : Nat) : (gamma^q)^4 * (64:ℝ)^q = (81:ℝ)^q := by
  rw [← pow_mul, Nat.mul_comm q 4, pow_mul, ← mul_pow, gamma_fourth]
  norm_num

/-- Exact equivalence between the integer fourth-power certificate and the
normalized real inequality. All scale factors are strictly positive. -/
theorem integer_bound_iff_normalized (z N q : Nat) :
    64^q*z^4 ≤ 2^N*81^q ↔ (z:ℝ)*t^N ≤ gamma^q := by
  have ht := t_pos
  have hg := gamma_pos
  have hfactor : 0 < (2:ℝ)^N*(64:ℝ)^q := by positivity
  have hleft : ((z:ℝ)*t^N)^4*((2:ℝ)^N*(64:ℝ)^q) = (64:ℝ)^q*(z:ℝ)^4 := by
    calc ((z:ℝ)*t^N)^4*((2:ℝ)^N*(64:ℝ)^q) =
          (64:ℝ)^q*(z:ℝ)^4*((t^N)^4*(2:ℝ)^N) := by ring
         _ = _ := by rw [t_power_cancel]; ring
  have hright : (gamma^q)^4*((2:ℝ)^N*(64:ℝ)^q) = (2:ℝ)^N*(81:ℝ)^q := by
    calc (gamma^q)^4*((2:ℝ)^N*(64:ℝ)^q) =
          (2:ℝ)^N*((gamma^q)^4*(64:ℝ)^q) := by ring
         _ = _ := by rw [gamma_power_cancel]
  have hpow : ((z:ℝ)*t^N)^4 ≤ (gamma^q)^4 ↔ (z:ℝ)*t^N ≤ gamma^q := by
    exact pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide)
  constructor
  · intro h
    have hr : (64:ℝ)^q*(z:ℝ)^4 ≤ (2:ℝ)^N*(81:ℝ)^q := by exact_mod_cast h
    apply hpow.mp
    apply (mul_le_mul_iff_left₀ hfactor).mp
    simpa only [hleft, hright] using hr
  · intro h
    have hp := mul_le_mul_of_nonneg_right (hpow.mpr h) hfactor.le
    rw [hleft, hright] at hp
    exact_mod_cast hp

theorem t_sq_mul_gamma : t^2*gamma = (3/4:ℝ) := by
  calc t^2*gamma = 3/2*t^4 := by unfold gamma; ring
       _ = 3/4 := by rw [t_fourth]; norm_num

theorem unmatched_coefficient_identity (d : Nat) :
    t^(1+2*d)*gamma^d = t*(3/4:ℝ)^d := by
  rw [pow_add, pow_one, pow_mul]
  calc t*(t^2)^d*gamma^d = t*(t^2*gamma)^d := by rw [mul_pow]; ring
       _ = _ := by rw [t_sq_mul_gamma]

end StableMatchingsE2E.StablePairCoefficients

namespace StableMatchingsE2E.LabeledMultigraph
open StablePairCoefficients
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

theorem sharpBound_iff_normalized (G : LabeledMultigraph V E) :
    G.SharpBound ↔ (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      gamma^G.doubleComponentCount :=
  integer_bound_iff_normalized _ _ _

theorem normalized_bound_at_larger_cost
    (G H : LabeledMultigraph V E) (k : Nat)
    (hcost : G.vertexCount+2*G.edgeCount = H.vertexCount+2*H.edgeCount+k)
    (hH : H.SharpBound) :
    (H.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤ t^k*gamma^H.doubleComponentCount := by
  have ht := t_pos
  have hn := (sharpBound_iff_normalized H).mp hH
  rw [hcost, pow_add]
  calc (H.matchingCount:ℝ)*(t^(H.vertexCount+2*H.edgeCount)*t^k) =
        ((H.matchingCount:ℝ)*t^(H.vertexCount+2*H.edgeCount))*t^k := by ring
       _ ≤ gamma^H.doubleComponentCount*t^k :=
         mul_le_mul_of_nonneg_right hn (by positivity)
       _ = _ := by ring

theorem normalized_delete_singleton_bound
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices)
    (hH : (G.deleteVertices {x}).SharpBound) :
    ((G.deleteVertices {x}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      t^(1+2*G.degree x)*gamma^(G.deleteVertices {x}).doubleComponentCount := by
  apply normalized_bound_at_larger_cost G _ _ _ hH
  have hv := vertexCount_delete_singleton_add_one G hx
  have he := edgeCount_delete_singleton_add_degree G x
  omega

theorem normalized_delete_pair_bound
    (G : LabeledMultigraph V E) {x y : V}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y)
    (hH : (G.deleteVertices {x,y}).SharpBound) :
    ((G.deleteVertices {x,y}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      t^(2+2*(G.degree x+G.degree y-G.multiplicity x y))*
        gamma^(G.deleteVertices {x,y}).doubleComponentCount := by
  apply normalized_bound_at_larger_cost G _ _ _ hH
  have hv := vertexCount_delete_pair_add_two G hx hy hxy
  have he := edgeCount_delete_pair_add_degrees G x y
  have ha := degree_delete_singleton_add_multiplicity G x y
  omega

theorem normalized_matching_recurrence
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices) :
    (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) =
      ((G.deleteVertices {x}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) +
      ∑ e ∈ G.incidentEdges x,
        ((G.deleteVertices (G.ends e)).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) := by
  rw [matchingCount_recurrence G hx]
  push_cast
  rw [add_mul, Finset.sum_mul]

theorem normalized_unmatched_bound_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected)
    {x : V} (hx : x ∈ G.vertices) (hH : (G.deleteVertices {x}).SharpBound) :
    ((G.deleteVertices {x}).matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) ≤
      t*(3/4:ℝ)^(G.degree x) := by
  have ht := t_pos
  have h := normalized_delete_singleton_bound G hx hH
  have hq := doubleComponentCount_delete_singleton_le_degree G hc hx
  have hp : gamma^(G.deleteVertices {x}).doubleComponentCount ≤ gamma^(G.degree x) :=
    pow_le_pow_right₀ gamma_gt_one.le hq
  calc _ ≤ t^(1+2*G.degree x)*gamma^(G.deleteVertices {x}).doubleComponentCount := h
       _ ≤ t^(1+2*G.degree x)*gamma^(G.degree x) :=
         mul_le_mul_of_nonneg_left hp (by positivity)
       _ = _ := unmatched_coefficient_identity _

end StableMatchingsE2E.LabeledMultigraph
