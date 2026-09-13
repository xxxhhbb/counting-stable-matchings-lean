import StableMatchingsE2E.StablePairTwoNeighbors

namespace StableMatchingsE2E.StablePairCoefficients

theorem integer_equality_iff_normalized (z N q : Nat) :
    64^q*z^4 = 2^N*81^q ↔ (z:ℝ)*t^N = gamma^q := by
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
  constructor
  · intro h
    have hr : (64:ℝ)^q*(z:ℝ)^4 = (2:ℝ)^N*(81:ℝ)^q := by exact_mod_cast h
    have hp : ((z:ℝ)*t^N)^4 = (gamma^q)^4 := by nlinarith [hleft, hright]
    apply le_antisymm
    · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp hp.le
    · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp hp.symm.le
  · intro h
    have hp : ((z:ℝ)*t^N)^4 = (gamma^q)^4 := congrArg (fun a : ℝ ↦ a^4) h
    have hr : (64:ℝ)^q*(z:ℝ)^4 = (2:ℝ)^N*(81:ℝ)^q := by rw [← hleft, ← hright, hp]
    exact_mod_cast hr

end StableMatchingsE2E.StablePairCoefficients

namespace StableMatchingsE2E.LabeledMultigraph
open StablePairCoefficients
variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

def SharpEquality (G : LabeledMultigraph V E) : Prop :=
  64^G.doubleComponentCount * G.matchingCount^4 =
    2^(G.vertexCount+2*G.edgeCount) * 81^G.doubleComponentCount

theorem sharpEquality_iff_normalized (G : LabeledMultigraph V E) :
    G.SharpEquality ↔ (G.matchingCount:ℝ)*t^(G.vertexCount+2*G.edgeCount) =
      gamma^G.doubleComponentCount := integer_equality_iff_normalized _ _ _

theorem not_sharpEquality_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected) (hv : 3 ≤ G.vertexCount) :
    ¬G.SharpEquality := by
  intro he
  have hn := (sharpEquality_iff_normalized G).mp he
  rw [doubleComponentCount_eq_zero_of_cutConnected G hc hv, pow_zero] at hn
  have hs := normalized_strict_of_cutConnected G hc hv
  linarith

theorem two_vertex_uncorrected_strict (k : Nat) (hk : 4 ≤ k) :
    (k+1)^4 < 2^(2+2*k) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hstep := fourth_power_growth j (by omega)
  have hbound := two_vertex_uncorrected_arithmetic j (by omega)
  have hexp : 2+2*(j+1) = (2+2*j)+2 := by omega
  rw [show j.succ = j+1 from rfl, hexp, pow_add]
  norm_num
  nlinarith

theorem sharpEquality_iff_of_vertexCount_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount = 2) :
    G.SharpEquality ↔ G.edgeCount = 1 ∨ G.edgeCount = 2 ∨ G.edgeCount = 3 := by
  unfold SharpEquality
  rw [matchingCount_eq_edgeCount_add_one_of_vertexCount_two G hv,
    doubleComponentCount_of_vertexCount_two G hv, hv]
  by_cases hsmall : G.edgeCount ≤ 3
  · interval_cases h : G.edgeCount <;> norm_num [h]
  · have hne : G.edgeCount ≠ 2 := by omega
    simp only [if_neg hne, pow_zero, one_mul, mul_one]
    have hs := two_vertex_uncorrected_strict G.edgeCount (by omega)
    constructor
    · intro he; omega
    · intro he; omega

theorem sharpEquality_iff_of_vertexCount_lt_two
    (G : LabeledMultigraph V E) (hv : G.vertexCount < 2) :
    G.SharpEquality ↔ G.vertexCount = 0 := by
  have he := edges_empty_of_vertexCount_lt_two G hv
  have hec : G.edgeCount = 0 := by simp [edgeCount, he]
  unfold SharpEquality
  rw [matchingCount_eq_one_of_edges_empty G he,
    doubleComponentCount_eq_zero_of_edges_empty G he, hec]
  interval_cases h : G.vertexCount <;> norm_num [h]

/-- Complete connected classification; the empty graph is cut-connected vacuously. -/
theorem sharpEquality_iff_of_cutConnected
    (G : LabeledMultigraph V E) (hc : G.CutConnected) :
    G.SharpEquality ↔ G.vertexCount = 0 ∨
      (G.vertexCount = 2 ∧ (G.edgeCount = 1 ∨ G.edgeCount = 2 ∨ G.edgeCount = 3)) := by
  by_cases hsmall : G.vertexCount < 2
  · rw [sharpEquality_iff_of_vertexCount_lt_two G hsmall]
    omega
  by_cases htwo : G.vertexCount = 2
  · rw [sharpEquality_iff_of_vertexCount_two G htwo]
    simp [htwo]
  have hlarge : 3 ≤ G.vertexCount := by omega
  have hn := not_sharpEquality_of_cutConnected G hc hlarge
  constructor
  · intro h; exact False.elim (hn h)
  · intro h; omega

theorem product_equality_iff (a b c d : Nat)
    (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hd : 0 < d) :
    a*b = c*d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    have hac : a=c := by
      by_contra hn
      have halt : a<c := by omega
      have hmul := Nat.mul_le_mul_left a hb
      have hstrict := Nat.mul_lt_mul_of_pos_right halt hd
      omega
    have hbd : b=d := by
      rw [hac] at h
      exact Nat.eq_of_mul_eq_mul_left hc h
    exact ⟨hac,hbd⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- Equality is preserved in both directions across an actual empty cut. -/
theorem sharpEquality_iff_of_empty_boundary
    (G : LabeledMultigraph V E) (D : Finset V) (hb : G.boundaryEdges D = ∅) :
    G.SharpEquality ↔ (G.deleteVertices D).SharpEquality ∧
      (G.deleteVertices (G.vertices \ D)).SharpEquality := by
  have hv := vertexCount_add_of_partition G D
  have he := edgeCount_add_of_empty_boundary G D hb
  have hq := doubleComponentCount_add_of_empty_boundary G D hb
  have hz := matchingCount_eq_mul_of_empty_boundary G D hb
  rw [Nat.mul_comm] at hz
  have hleft := sharpBound (G.deleteVertices D)
  have hright := sharpBound (G.deleteVertices (G.vertices \ D))
  unfold SharpBound at hleft hright
  have hp := product_equality_iff _ _ _ _ hleft hright (by positivity) (by positivity)
  unfold SharpEquality
  constructor
  · intro h
    apply hp.mp
    rw [← hv, ← he, ← hq, hz] at h
    simp only [pow_add, mul_pow] at h
    convert h using 1 <;> ring
  · intro h
    have hh := hp.mpr h
    rw [← hv, ← he, ← hq, hz]
    simp only [pow_add, mul_pow]
    convert hh using 1 <;> ring

/-- A finite decomposition into two-vertex, one/two/three-label components.
Every split is a genuine proper empty cut in the original graph. -/
inductive PairComponentDecomposition : LabeledMultigraph V E → Prop
  | empty (G : LabeledMultigraph V E) (hv : G.vertexCount = 0) :
      PairComponentDecomposition G
  | pair (G : LabeledMultigraph V E) (hv : G.vertexCount = 2)
      (he : G.edgeCount = 1 ∨ G.edgeCount = 2 ∨ G.edgeCount = 3) :
      PairComponentDecomposition G
  | split (G : LabeledMultigraph V E) (D : Finset V)
      (hsub : D ⊆ G.vertices) (hn : D.Nonempty) (hn' : (G.vertices \ D).Nonempty)
      (hb : G.boundaryEdges D = ∅)
      (left : PairComponentDecomposition (G.deleteVertices D))
      (right : PairComponentDecomposition (G.deleteVertices (G.vertices \ D))) :
      PairComponentDecomposition G

theorem sharpEquality_of_pairComponentDecomposition
    {G : LabeledMultigraph V E} (h : G.PairComponentDecomposition) : G.SharpEquality := by
  induction h with
  | empty H hv => exact (sharpEquality_iff_of_vertexCount_lt_two H (by omega)).mpr hv
  | pair H hv he => exact (sharpEquality_iff_of_vertexCount_two H hv).mpr he
  | split H D hsub hn hn' hb left right ihl ihr =>
    exact (sharpEquality_iff_of_empty_boundary H D hb).mpr ⟨ihl,ihr⟩

/-- Full multigraph equality classification, represented by a certified
component-decomposition tree rather than an assumed graph component API. -/
theorem sharpEquality_iff_pairComponentDecomposition (G : LabeledMultigraph V E) :
    G.SharpEquality ↔ G.PairComponentDecomposition := by
  classical
  refine ⟨?_, sharpEquality_of_pairComponentDecomposition⟩
  have hall : ∀ n, ∀ H : LabeledMultigraph V E, H.vertexCount = n →
      H.SharpEquality → H.PairComponentDecomposition := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hn hEq
      by_cases hc : H.CutConnected
      · rcases (sharpEquality_iff_of_cutConnected H hc).mp hEq with hzero | ⟨htwo,he⟩
        · exact PairComponentDecomposition.empty H hzero
        · exact PairComponentDecomposition.pair H htwo he
      · obtain ⟨D,hsub,hD,hcomp,hb⟩ := exists_split_of_not_cutConnected H hc
        have hsum := vertexCount_add_of_partition H D
        have hleft : 0 < (H.deleteVertices D).vertexCount := Finset.card_pos.mpr hcomp
        have hright : 0 < (H.deleteVertices (H.vertices \ D)).vertexCount := by
          apply Finset.card_pos.mpr
          obtain ⟨v,hv⟩ := hD
          refine ⟨v,Finset.mem_sdiff.mpr ⟨hsub hv,?_⟩⟩
          exact fun h ↦ (Finset.mem_sdiff.mp h).2 hv
        have hparts := (sharpEquality_iff_of_empty_boundary H D hb).mp hEq
        exact PairComponentDecomposition.split H D hsub hD hcomp hb
          (ih _ (by omega) _ rfl hparts.1) (ih _ (by omega) _ rfl hparts.2)
  exact hall G.vertexCount G rfl

end StableMatchingsE2E.LabeledMultigraph
