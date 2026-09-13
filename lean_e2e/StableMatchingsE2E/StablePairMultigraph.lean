import StableMatchingsE2E.StablePairHypergraph

/-!
# Finite labeled loopless multigraph states

The vertex and edge types are fixed ambient finite types; a graph state
stores active finite sets.  This makes vertex deletion an operation within
one type, which is convenient for the matching recurrence used in the sharp
stable-pair bound.
-/

namespace StableMatchingsE2E

/-- A finite labeled loopless multigraph.  Parallel edge labels are kept
distinct. -/
structure LabeledMultigraph (V E : Type) where
  vertices : Finset V
  edges : Finset E
  ends : E → Finset V
  ends_card : ∀ e ∈ edges, (ends e).card = 2
  ends_subset : ∀ e ∈ edges, ends e ⊆ vertices

namespace LabeledMultigraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

def toHypergraph (G : LabeledMultigraph V E) : LabeledHypergraph V E where
  support := G.ends

/-- A graph matching uses active labels only and has disjoint endpoints. -/
def IsMatching (G : LabeledMultigraph V E) (S : Finset E) : Prop :=
  S ⊆ G.edges ∧ G.toHypergraph.IsMatching S

instance (G : LabeledMultigraph V E) (S : Finset E) :
    Decidable (G.IsMatching S) := by
  unfold IsMatching
  infer_instance

def matchingFamily (G : LabeledMultigraph V E) : Finset (Finset E) :=
  Finset.univ.filter G.IsMatching

def matchingCount (G : LabeledMultigraph V E) : Nat :=
  G.matchingFamily.card

@[simp] theorem mem_matchingFamily_iff (G : LabeledMultigraph V E)
    (S : Finset E) : S ∈ G.matchingFamily ↔ G.IsMatching S := by
  simp [matchingFamily]

def vertexCount (G : LabeledMultigraph V E) : Nat := G.vertices.card

def edgeCount (G : LabeledMultigraph V E) : Nat := G.edges.card

def incidentEdges (G : LabeledMultigraph V E) (x : V) : Finset E :=
  G.edges.filter fun e ↦ x ∈ G.ends e

def degree (G : LabeledMultigraph V E) (x : V) : Nat :=
  (G.incidentEdges x).card

/-- Active labels joining the two distinct named endpoints. -/
def edgesBetween (G : LabeledMultigraph V E) (x y : V) : Finset E :=
  G.edges.filter fun e ↦ x ∈ G.ends e ∧ y ∈ G.ends e

def multiplicity (G : LabeledMultigraph V E) (x y : V) : Nat :=
  (G.edgesBetween x y).card

@[simp] theorem mem_incidentEdges_iff (G : LabeledMultigraph V E)
    (x : V) (e : E) :
    e ∈ G.incidentEdges x ↔ e ∈ G.edges ∧ x ∈ G.ends e := by
  simp [incidentEdges]

@[simp] theorem mem_edgesBetween_iff (G : LabeledMultigraph V E)
    (x y : V) (e : E) :
    e ∈ G.edgesBetween x y ↔
      e ∈ G.edges ∧ x ∈ G.ends e ∧ y ∈ G.ends e := by
  simp [edgesBetween]

/-- A label set avoids deleted vertices if every selected edge is disjoint
from the deleted set. -/
def Avoids (G : LabeledMultigraph V E) (D : Finset V)
    (S : Finset E) : Prop :=
  ∀ e ∈ S, Disjoint (G.ends e) D

instance (G : LabeledMultigraph V E) (D : Finset V) (S : Finset E) :
    Decidable (G.Avoids D S) := by
  unfold Avoids
  infer_instance

/-- Delete vertices and every active edge meeting them. -/
def deleteVertices (G : LabeledMultigraph V E) (D : Finset V) :
    LabeledMultigraph V E where
  vertices := G.vertices \ D
  edges := G.edges.filter fun e ↦ Disjoint (G.ends e) D
  ends := G.ends
  ends_card := by
    intro e he
    exact G.ends_card e (Finset.mem_filter.1 he).1
  ends_subset := by
    intro e he v hve
    have hedge := Finset.mem_filter.1 he
    rw [Finset.mem_sdiff]
    refine ⟨G.ends_subset e hedge.1 hve, ?_⟩
    rw [Finset.disjoint_left] at hedge
    exact fun hvD ↦ hedge.2 hve hvD

@[simp] theorem mem_deleteVertices_edges_iff
    (G : LabeledMultigraph V E) (D : Finset V) (e : E) :
    e ∈ (G.deleteVertices D).edges ↔
      e ∈ G.edges ∧ Disjoint (G.ends e) D := by
  simp [deleteVertices]

theorem deleteVertices_isMatching_iff
    (G : LabeledMultigraph V E) (D : Finset V) (S : Finset E) :
    (G.deleteVertices D).IsMatching S ↔
      G.IsMatching S ∧ G.Avoids D S := by
  constructor
  · rintro ⟨hactive, hmatching⟩
    refine ⟨⟨?_, hmatching⟩, ?_⟩
    · intro e he
      exact (Finset.mem_filter.1 (hactive he)).1
    · intro e he
      exact (Finset.mem_filter.1 (hactive he)).2
  · rintro ⟨⟨hactive, hmatching⟩, havoid⟩
    refine ⟨?_, hmatching⟩
    intro e he
    exact Finset.mem_filter.2 ⟨hactive he, havoid e he⟩

theorem matchingFamily_deleteVertices_eq_filter
    (G : LabeledMultigraph V E) (D : Finset V) :
    (G.deleteVertices D).matchingFamily =
      G.matchingFamily.filter (G.Avoids D) := by
  ext S
  simp [deleteVertices_isMatching_iff]

theorem matchingCount_deleteVertices_eq_card_filter
    (G : LabeledMultigraph V E) (D : Finset V) :
    (G.deleteVertices D).matchingCount =
      (G.matchingFamily.filter (G.Avoids D)).card := by
  rw [matchingCount, matchingFamily_deleteVertices_eq_filter]

def containingFamily (G : LabeledMultigraph V E) (e : E) :
    Finset (Finset E) :=
  G.matchingFamily.filter fun S ↦ e ∈ S

def unmatchedAtFamily (G : LabeledMultigraph V E) (x : V) :
    Finset (Finset E) :=
  G.matchingFamily.filter (G.Avoids {x})

def matchedAtFamily (G : LabeledMultigraph V E) (x : V) :
    Finset (Finset E) :=
  G.matchingFamily.filter fun S ↦ ¬G.Avoids {x} S

theorem unmatchedAt_card_add_matchedAt_card
    (G : LabeledMultigraph V E) (x : V) :
    (G.unmatchedAtFamily x).card + (G.matchedAtFamily x).card =
      G.matchingCount := by
  exact Finset.filter_card_add_filter_neg_card_eq_card (G.Avoids {x})

theorem matchedAtFamily_eq_biUnion_containing
    (G : LabeledMultigraph V E) (x : V) :
    G.matchedAtFamily x =
      (G.incidentEdges x).biUnion G.containingFamily := by
  ext S
  constructor
  · intro hS
    have hS' : S ∈ G.matchingFamily ∧ ¬G.Avoids {x} S := by
      simpa [matchedAtFamily] using hS
    have hmatching := (mem_matchingFamily_iff G S).1 hS'.1
    have hhit : ∃ e ∈ S, x ∈ G.ends e := by
      simpa [Avoids, Finset.disjoint_singleton_right] using hS'.2
    obtain ⟨e, heS, hxe⟩ := hhit
    rw [Finset.mem_biUnion]
    refine ⟨e, (mem_incidentEdges_iff G x e).2
      ⟨hmatching.1 heS, hxe⟩, ?_⟩
    simp [containingFamily, hS'.1, heS]
  · intro hS
    rw [Finset.mem_biUnion] at hS
    obtain ⟨e, heInc, heFamily⟩ := hS
    have heFamily' : S ∈ G.matchingFamily ∧ e ∈ S := by
      simpa [containingFamily] using heFamily
    have hxe := (mem_incidentEdges_iff G x e).1 heInc |>.2
    simp only [matchedAtFamily, Finset.mem_filter]
    refine ⟨heFamily'.1, ?_⟩
    simp [Avoids, Finset.disjoint_singleton_right]
    exact ⟨e, heFamily'.2, hxe⟩

theorem containingFamily_pairwiseDisjoint_at
    (G : LabeledMultigraph V E) (x : V) :
    (↑(G.incidentEdges x) : Set E).PairwiseDisjoint G.containingFamily := by
  intro e he f hf hef
  change Disjoint (G.containingFamily e) (G.containingFamily f)
  rw [Finset.disjoint_left]
  intro S hSe hSf
  have hSe' := Finset.mem_filter.1 hSe
  have hSf' := Finset.mem_filter.1 hSf
  have hmatching := (mem_matchingFamily_iff G S).1 hSe'.1
  have hxe := (mem_incidentEdges_iff G x e).1 he |>.2
  have hxf := (mem_incidentEdges_iff G x f).1 hf |>.2
  have hdis := hmatching.2 e hSe'.2 f hSf'.2 hef
  rw [Finset.disjoint_left] at hdis
  exact hdis hxe hxf

theorem matchedAt_card_eq_sum_containing
    (G : LabeledMultigraph V E) (x : V) :
    (G.matchedAtFamily x).card =
      ∑ e ∈ G.incidentEdges x, (G.containingFamily e).card := by
  rw [matchedAtFamily_eq_biUnion_containing]
  exact Finset.card_biUnion (containingFamily_pairwiseDisjoint_at G x)

private theorem edge_not_mem_delete_own_ends
    (G : LabeledMultigraph V E) {e : E} (he : e ∈ G.edges) :
    e ∉ (G.deleteVertices (G.ends e)).edges := by
  intro hmem
  have hdis := (mem_deleteVertices_edges_iff G (G.ends e) e).1 hmem |>.2
  have hnonempty : (G.ends e).Nonempty := by
    rw [← Finset.card_pos]
    rw [G.ends_card e he]
    norm_num
  obtain ⟨v, hv⟩ := hnonempty
  rw [Finset.disjoint_left] at hdis
  exact hdis hv hv

private theorem insert_edge_isMatching
    (G : LabeledMultigraph V E) {e : E} (he : e ∈ G.edges)
    {T : Finset E}
    (hT : (G.deleteVertices (G.ends e)).IsMatching T) :
    G.IsMatching (insert e T) := by
  have hT' := (deleteVertices_isMatching_iff G (G.ends e) T).1 hT
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact he
    · exact hT'.1.1 hf
  · intro f hf g hg hfg
    rw [Finset.mem_insert] at hf hg
    rcases hf with rfl | hf <;> rcases hg with rfl | hg
    · exact False.elim (hfg rfl)
    · exact (hT'.2 g hg).symm
    · exact hT'.2 f hf
    · exact hT'.1.2 f hf g hg hfg

/-- Matchings containing a fixed active label are in bijection with
matchings after deleting that label's two endpoints. -/
theorem containingFamily_card_eq_deleteVertices
    (G : LabeledMultigraph V E) {e : E} (he : e ∈ G.edges) :
    (G.containingFamily e).card =
      (G.deleteVertices (G.ends e)).matchingCount := by
  rw [matchingCount]
  apply Finset.card_bij (fun S _ ↦ S.erase e)
  · intro S hS
    have hS' : S ∈ G.matchingFamily ∧ e ∈ S := by
      simpa [containingFamily] using hS
    have hSmatching := (mem_matchingFamily_iff G S).1 hS'.1
    rw [mem_matchingFamily_iff]
    apply (deleteVertices_isMatching_iff G (G.ends e) (S.erase e)).2
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro f hf
        exact hSmatching.1 (Finset.mem_of_mem_erase hf)
      · intro f hf g hg hfg
        exact hSmatching.2 f (Finset.mem_of_mem_erase hf)
          g (Finset.mem_of_mem_erase hg) hfg
    · intro f hf
      have hfS := Finset.mem_of_mem_erase hf
      have hfe : f ≠ e := Finset.ne_of_mem_erase hf
      exact hSmatching.2 f hfS e hS'.2 hfe
  · intro S hS T hT hEq
    have hSmem : S ∈ G.matchingFamily ∧ e ∈ S := by
      simpa [containingFamily] using hS
    have hTmem : T ∈ G.matchingFamily ∧ e ∈ T := by
      simpa [containingFamily] using hT
    have heS : e ∈ S := hSmem.2
    have heT : e ∈ T := hTmem.2
    calc
      S = insert e (S.erase e) := (Finset.insert_erase heS).symm
      _ = insert e (T.erase e) := congrArg (insert e) hEq
      _ = T := Finset.insert_erase heT
  · intro T hT
    have hTmatching := (mem_matchingFamily_iff _ _).1 hT
    have heT : e ∉ T := by
      intro hemem
      exact edge_not_mem_delete_own_ends G he
        (hTmatching.1 hemem)
    refine ⟨insert e T, ?_, ?_⟩
    · simp only [containingFamily, Finset.mem_filter]
      exact ⟨(mem_matchingFamily_iff G _).2
          (insert_edge_isMatching G he hTmatching),
        Finset.mem_insert_self e T⟩
    · exact Finset.erase_insert heT

/-- Exact labeled-edge matching recurrence at an active vertex. -/
theorem matchingCount_recurrence
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices) :
    G.matchingCount =
      (G.deleteVertices {x}).matchingCount +
        ∑ e ∈ G.incidentEdges x,
          (G.deleteVertices (G.ends e)).matchingCount := by
  have hunmatched : (G.unmatchedAtFamily x).card =
      (G.deleteVertices {x}).matchingCount := by
    rw [matchingCount_deleteVertices_eq_card_filter]
    rfl
  have hmatched := matchedAt_card_eq_sum_containing G x
  have hpartition := unmatchedAt_card_add_matchedAt_card G x
  rw [hunmatched, hmatched] at hpartition
  have hedge : ∀ e ∈ G.incidentEdges x,
      (G.containingFamily e).card =
        (G.deleteVertices (G.ends e)).matchingCount := by
    intro e he
    exact containingFamily_card_eq_deleteVertices G
      ((mem_incidentEdges_iff G x e).1 he |>.1)
  rw [Finset.sum_congr rfl hedge] at hpartition
  exact hpartition.symm

/-- Active labels whose endpoint set is exactly `s`. -/
def edgesOn (G : LabeledMultigraph V E) (s : Finset V) : Finset E :=
  G.edges.filter fun e ↦ G.ends e = s

/-- `s` is isolated from every active edge not supported exactly on `s`. -/
def IsIsolatedSupport (G : LabeledMultigraph V E) (s : Finset V) : Prop :=
  s ⊆ G.vertices ∧
    ∀ e ∈ G.edges, ¬Disjoint (G.ends e) s → G.ends e = s

instance (G : LabeledMultigraph V E) (s : Finset V) :
    Decidable (G.IsIsolatedSupport s) := by
  unfold IsIsolatedSupport
  infer_instance

/-- An exceptional component is an isolated two-vertex support carrying
exactly two active labeled edges. -/
def IsDoubleComponent (G : LabeledMultigraph V E) (s : Finset V) : Prop :=
  s.card = 2 ∧ G.IsIsolatedSupport s ∧ (G.edgesOn s).card = 2

instance (G : LabeledMultigraph V E) (s : Finset V) :
    Decidable (G.IsDoubleComponent s) := by
  unfold IsDoubleComponent
  infer_instance

def doubleComponents (G : LabeledMultigraph V E) : Finset (Finset V) :=
  G.vertices.powerset.filter G.IsDoubleComponent

def doubleComponentCount (G : LabeledMultigraph V E) : Nat :=
  G.doubleComponents.card

@[simp] theorem mem_doubleComponents_iff
    (G : LabeledMultigraph V E) (s : Finset V) :
    s ∈ G.doubleComponents ↔ s ⊆ G.vertices ∧ G.IsDoubleComponent s := by
  simp [doubleComponents]

/-- Distinct exceptional double components have disjoint vertex supports. -/
theorem disjoint_of_isDoubleComponent
    (G : LabeledMultigraph V E) {s t : Finset V}
    (hs : G.IsDoubleComponent s) (ht : G.IsDoubleComponent t)
    (hst : s ≠ t) : Disjoint s t := by
  classical
  by_contra hmeet
  have hedgesNonempty : (G.edgesOn s).Nonempty := by
    rw [← Finset.card_pos, hs.2.2]
    norm_num
  obtain ⟨e, he⟩ := hedgesNonempty
  have he' : e ∈ G.edges ∧ G.ends e = s := by
    simpa [edgesOn] using he
  have hmeet' : ¬Disjoint (G.ends e) t := by
    simpa [he'.2] using hmeet
  have het : G.ends e = t := ht.2.1.2 e he'.1 hmeet'
  exact hst (he'.2.symm.trans het)

theorem doubleComponents_pairwiseDisjoint
    (G : LabeledMultigraph V E) :
    (↑G.doubleComponents : Set (Finset V)).PairwiseDisjoint id := by
  intro s hs t ht hst
  change Disjoint s t
  exact disjoint_of_isDoubleComponent G
    ((mem_doubleComponents_iff G s).1 hs).2
    ((mem_doubleComponents_iff G t).1 ht).2 hst

/-- Active edges removed by deleting `D`. -/
def crossingDeletedEdges (G : LabeledMultigraph V E) (D : Finset V) : Finset E :=
  G.edges.filter fun e ↦ ¬Disjoint (G.ends e) D

@[simp] theorem mem_crossingDeletedEdges_iff
    (G : LabeledMultigraph V E) (D : Finset V) (e : E) :
    e ∈ G.crossingDeletedEdges D ↔
      e ∈ G.edges ∧ ¬Disjoint (G.ends e) D := by
  simp [crossingDeletedEdges]

/-- Active cut edges, i.e. active labels with one endpoint in `D` and one
endpoint in the active complement. -/
def boundaryEdges (G : LabeledMultigraph V E) (D : Finset V) : Finset E :=
  G.edges.filter fun e ↦
    ¬Disjoint (G.ends e) D ∧
      ¬Disjoint (G.ends e) (G.vertices \ D)

@[simp] theorem mem_boundaryEdges_iff
    (G : LabeledMultigraph V E) (D : Finset V) (e : E) :
    e ∈ G.boundaryEdges D ↔
      e ∈ G.edges ∧ ¬Disjoint (G.ends e) D ∧
        ¬Disjoint (G.ends e) (G.vertices \ D) := by
  simp [boundaryEdges]

theorem boundaryEdges_singleton_eq_incidentEdges
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices) :
    G.boundaryEdges {x} = G.incidentEdges x := by
  classical
  ext e
  constructor
  · intro he
    have he' := (mem_boundaryEdges_iff G {x} e).1 he
    rw [Finset.not_disjoint_iff] at he'
    obtain ⟨v, hve, hvx⟩ := he'.2.1
    have hvEq : v = x := by simpa using hvx
    exact (mem_incidentEdges_iff G x e).2 ⟨he'.1, hvEq ▸ hve⟩
  · intro he
    have he' := (mem_incidentEdges_iff G x e).1 he
    have hcardErase : ((G.ends e).erase x).card = 1 := by
      rw [Finset.card_erase_of_mem he'.2, G.ends_card e he'.1]
    have heraseNonempty : ((G.ends e).erase x).Nonempty := by
      rw [← Finset.card_pos, hcardErase]
      norm_num
    obtain ⟨y, hyErase⟩ := heraseNonempty
    have hyEnds : y ∈ G.ends e := Finset.mem_of_mem_erase hyErase
    have hyNe : y ≠ x := Finset.ne_of_mem_erase hyErase
    apply (mem_boundaryEdges_iff G {x} e).2
    refine ⟨he'.1, ?_, ?_⟩
    · rw [Finset.not_disjoint_iff]
      exact ⟨x, he'.2, by simp⟩
    · rw [Finset.not_disjoint_iff]
      exact ⟨y, hyEnds, Finset.mem_sdiff.2
        ⟨G.ends_subset e he'.1 hyEnds, by simpa using hyNe⟩⟩

@[simp] theorem boundaryEdges_singleton_card
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices) :
    (G.boundaryEdges {x}).card = G.degree x := by
  rw [boundaryEdges_singleton_eq_incidentEdges G hx]
  rfl

private theorem ends_eq_pair_of_both_mem
    (G : LabeledMultigraph V E) {e : E} (he : e ∈ G.edges)
    {x y : V} (hxy : x ≠ y) (hxe : x ∈ G.ends e)
    (hye : y ∈ G.ends e) : G.ends e = {x, y} := by
  have hsub : ({x, y} : Finset V) ⊆ G.ends e := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxe, hye⟩
  have hcardPair : ({x, y} : Finset V).card = 2 := by
    simp [hxy]
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [G.ends_card e he, hcardPair])).symm

private theorem mem_boundaryEdges_pair_of_incident_not_incident
    (G : LabeledMultigraph V E) {x y : V} (hxy : x ≠ y)
    {e : E} (hex : e ∈ G.incidentEdges x)
    (hey : e ∉ G.incidentEdges y) : e ∈ G.boundaryEdges {x, y} := by
  classical
  have hex' := (mem_incidentEdges_iff G x e).1 hex
  have hyNotEnds : y ∉ G.ends e := fun hye ↦
    hey ((mem_incidentEdges_iff G y e).2 ⟨hex'.1, hye⟩)
  have hcardErase : ((G.ends e).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hex'.2, G.ends_card e hex'.1]
  have heraseNonempty : ((G.ends e).erase x).Nonempty := by
    rw [← Finset.card_pos, hcardErase]
    norm_num
  obtain ⟨z, hzErase⟩ := heraseNonempty
  have hzEnds : z ∈ G.ends e := Finset.mem_of_mem_erase hzErase
  have hzNeX : z ≠ x := Finset.ne_of_mem_erase hzErase
  have hzNeY : z ≠ y := fun h ↦ hyNotEnds (h ▸ hzEnds)
  apply (mem_boundaryEdges_iff G {x, y} e).2
  refine ⟨hex'.1, ?_, ?_⟩
  · rw [Finset.not_disjoint_iff]
    exact ⟨x, hex'.2, by simp⟩
  · rw [Finset.not_disjoint_iff]
    refine ⟨z, hzEnds, Finset.mem_sdiff.2
      ⟨G.ends_subset e hex'.1 hzEnds, ?_⟩⟩
    simp [hzNeX, hzNeY]

/-- The boundary of a two-vertex set is the disjoint union of labels
incident to exactly one of its two vertices. -/
theorem boundaryEdges_pair_eq
    (G : LabeledMultigraph V E) {x y : V} (hxy : x ≠ y) :
    G.boundaryEdges {x, y} =
      (G.incidentEdges x \ G.incidentEdges y) ∪
        (G.incidentEdges y \ G.incidentEdges x) := by
  classical
  ext e
  constructor
  · intro he
    have he' := (mem_boundaryEdges_iff G {x, y} e).1 he
    rw [Finset.not_disjoint_iff] at he'
    obtain ⟨z, hze, hzPair⟩ := he'.2.1
    have hzCases : z = x ∨ z = y := by simpa using hzPair
    have hnotBoth : ¬(x ∈ G.ends e ∧ y ∈ G.ends e) := by
      rintro ⟨hxe, hye⟩
      have hends := ends_eq_pair_of_both_mem G he'.1 hxy hxe hye
      rw [hends, Finset.not_disjoint_iff] at he'
      obtain ⟨w, hwPair, hwOutside⟩ := he'.2.2
      exact (Finset.mem_sdiff.1 hwOutside).2 hwPair
    rcases hzCases with hzEq | hzEq
    · have hex : e ∈ G.incidentEdges x :=
        (mem_incidentEdges_iff G x e).2 ⟨he'.1, hzEq ▸ hze⟩
      have hey : e ∉ G.incidentEdges y := by
        intro hey
        exact hnotBoth ⟨hzEq ▸ hze,
          (mem_incidentEdges_iff G y e).1 hey |>.2⟩
      simp [hex, hey]
    · have hey : e ∈ G.incidentEdges y :=
        (mem_incidentEdges_iff G y e).2 ⟨he'.1, hzEq ▸ hze⟩
      have hex : e ∉ G.incidentEdges x := by
        intro hex
        exact hnotBoth ⟨(mem_incidentEdges_iff G x e).1 hex |>.2,
          hzEq ▸ hze⟩
      simp [hex, hey]
  · intro he
    simp only [Finset.mem_union, Finset.mem_sdiff] at he
    rcases he with ⟨hex, hey⟩ | ⟨hey, hex⟩
    · exact mem_boundaryEdges_pair_of_incident_not_incident G hxy hex hey
    · simpa [Finset.pair_comm] using
        (mem_boundaryEdges_pair_of_incident_not_incident G hxy.symm hey hex)

theorem edgesBetween_eq_inter_incidentEdges
    (G : LabeledMultigraph V E) (x y : V) :
    G.edgesBetween x y = G.incidentEdges x ∩ G.incidentEdges y := by
  ext e
  simp only [mem_edgesBetween_iff, Finset.mem_inter, mem_incidentEdges_iff]
  tauto

/-- Exact cut-size identity used in the two-endpoint deletion branch:
`|δ({x,y})| + 2 a_xy = d(x)+d(y)`. -/
theorem boundaryEdges_pair_card_add_twice_multiplicity
    (G : LabeledMultigraph V E) {x y : V} (hxy : x ≠ y) :
    (G.boundaryEdges {x, y}).card + 2 * G.multiplicity x y =
      G.degree x + G.degree y := by
  classical
  rw [boundaryEdges_pair_eq G hxy]
  have hdis : Disjoint
      (G.incidentEdges x \ G.incidentEdges y)
      (G.incidentEdges y \ G.incidentEdges x) := by
    rw [Finset.disjoint_left]
    intro e heX heY
    exact (Finset.mem_sdiff.1 heX).2 (Finset.mem_sdiff.1 heY).1
  rw [Finset.card_union_of_disjoint hdis]
  rw [Finset.card_sdiff, Finset.card_sdiff]
  have hinterXY := edgesBetween_eq_inter_incidentEdges G x y
  have hinterYX := edgesBetween_eq_inter_incidentEdges G y x
  have hmultSym : G.multiplicity y x = G.multiplicity x y := by
    unfold multiplicity
    rw [hinterYX, hinterXY, Finset.inter_comm]
  have hmulLeX : G.multiplicity x y ≤ G.degree x := by
    unfold multiplicity degree
    rw [hinterXY]
    exact Finset.card_le_card Finset.inter_subset_left
  have hmulLeY : G.multiplicity x y ≤ G.degree y := by
    unfold multiplicity degree
    rw [hinterXY]
    exact Finset.card_le_card Finset.inter_subset_right
  rw [← hinterYX, ← hinterXY]
  change
    (G.degree x - G.multiplicity y x) +
      (G.degree y - G.multiplicity x y) +
        2 * G.multiplicity x y = G.degree x + G.degree y
  rw [hmultSym]
  omega

/-- Every exceptional component left after deleting `D` has an original
active edge that meets both `D` and that residual component.  Connectivity
will later imply this cut-witness condition. -/
def DeletionWitnessed (G : LabeledMultigraph V E) (D : Finset V) : Prop :=
  ∀ s ∈ (G.deleteVertices D).doubleComponents,
    ∃ e ∈ G.boundaryEdges D, ¬Disjoint (G.ends e) s

/-- A two-ended edge meeting `D` cannot also meet two distinct residual
double components.  This is the local injectivity fact behind the charge for
new exceptional components. -/
theorem crossing_edge_meets_at_most_one_doubleComponent
    (G : LabeledMultigraph V E) (D : Finset V)
    {e : E} (he : e ∈ G.crossingDeletedEdges D)
    {s t : Finset V}
    (hs : s ∈ (G.deleteVertices D).doubleComponents)
    (ht : t ∈ (G.deleteVertices D).doubleComponents)
    (hes : ¬Disjoint (G.ends e) s)
    (het : ¬Disjoint (G.ends e) t) : s = t := by
  classical
  by_contra hst
  have hstDisjoint : Disjoint s t :=
    disjoint_of_isDoubleComponent (G.deleteVertices D)
      ((mem_doubleComponents_iff _ s).1 hs).2
      ((mem_doubleComponents_iff _ t).1 ht).2 hst
  have hsSub : s ⊆ G.vertices \ D :=
    (mem_doubleComponents_iff (G.deleteVertices D) s).1 hs |>.1
  have htSub : t ⊆ G.vertices \ D :=
    (mem_doubleComponents_iff (G.deleteVertices D) t).1 ht |>.1
  have he' := (mem_crossingDeletedEdges_iff G D e).1 he
  rw [Finset.not_disjoint_iff] at he'
  rw [Finset.not_disjoint_iff] at hes het
  obtain ⟨d, hde, hdD⟩ := he'.2
  obtain ⟨u, hue, hus⟩ := hes
  obtain ⟨v, hve, hvt⟩ := het
  have huNotD : u ∉ D := (Finset.mem_sdiff.1 (hsSub hus)).2
  have hvNotD : v ∉ D := (Finset.mem_sdiff.1 (htSub hvt)).2
  have hdu : d ≠ u := fun h ↦ huNotD (h ▸ hdD)
  have hdv : d ≠ v := fun h ↦ hvNotD (h ▸ hdD)
  have huv : u ≠ v := by
    intro huv
    rw [Finset.disjoint_left] at hstDisjoint
    exact hstDisjoint hus (huv ▸ hvt)
  have hthreeSub : ({d, u, v} : Finset V) ⊆ G.ends e := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hde, hue, hve⟩
  have hthreeCard : ({d, u, v} : Finset V).card = 3 := by
    simp [hdu, hdv, huv]
  have hle := Finset.card_le_card hthreeSub
  rw [hthreeCard, G.ends_card e he'.1] at hle
  omega

/-- The cut-witness condition gives an injection from every exceptional
component created by deletion to a distinct removed active edge. -/
theorem doubleComponentCount_deleteVertices_le_crossingDeletedEdges
    (G : LabeledMultigraph V E) (D : Finset V)
    (hw : G.DeletionWitnessed D) :
    (G.deleteVertices D).doubleComponentCount ≤
      (G.boundaryEdges D).card := by
  classical
  let chooseEdge :
      (s : ↥(G.deleteVertices D).doubleComponents) →
        ↥(G.boundaryEdges D) := fun s ↦
    ⟨Classical.choose (hw s.1 s.2),
      (Classical.choose_spec (hw s.1 s.2)).1⟩
  have hinj : Function.Injective chooseEdge := by
    intro s t het
    have heVal : (chooseEdge s).1 = (chooseEdge t).1 :=
      congrArg Subtype.val het
    apply Subtype.ext
    apply crossing_edge_meets_at_most_one_doubleComponent G D
      ((mem_crossingDeletedEdges_iff G D _).2
        ⟨(mem_boundaryEdges_iff G D _).1 (chooseEdge s).2 |>.1,
          (mem_boundaryEdges_iff G D _).1 (chooseEdge s).2 |>.2.1⟩)
      s.2 t.2
    · exact (Classical.choose_spec (hw s.1 s.2)).2
    · have htMeet := (Classical.choose_spec (hw t.1 t.2)).2
      change ¬Disjoint (G.ends (chooseEdge t).1) t.1 at htMeet
      rw [← heVal] at htMeet
      exact htMeet
  simpa only [doubleComponentCount, Fintype.card_coe] using
    (Fintype.card_le_of_injective chooseEdge hinj)

/-- Cut formulation of connectedness for the active graph.  It avoids any
choice of paths and is exactly the fact needed by the deletion induction. -/
def CutConnected (G : LabeledMultigraph V E) : Prop :=
  ∀ s : Finset V, s ⊆ G.vertices → s.Nonempty →
    (G.vertices \ s).Nonempty →
    ∃ e ∈ G.edges,
      ¬Disjoint (G.ends e) s ∧
        ¬Disjoint (G.ends e) (G.vertices \ s)

/-- In a cut-connected graph, every exceptional component remaining after a
nonempty vertex deletion is witnessed by an original edge crossing the
deleted set. -/
theorem deletionWitnessed_of_cutConnected
    (G : LabeledMultigraph V E) (D : Finset V)
    (hconn : G.CutConnected) (hDsub : D ⊆ G.vertices)
    (hDnonempty : D.Nonempty) : G.DeletionWitnessed D := by
  classical
  intro s hs
  have hsInfo := (mem_doubleComponents_iff (G.deleteVertices D) s).1 hs
  have hsSubResidual : s ⊆ G.vertices \ D := hsInfo.1
  have hsSub : s ⊆ G.vertices := fun v hv ↦
    (Finset.mem_sdiff.1 (hsSubResidual hv)).1
  have hsNonempty : s.Nonempty := by
    rw [← Finset.card_pos, hsInfo.2.1]
    norm_num
  have hcomplementNonempty : (G.vertices \ s).Nonempty := by
    obtain ⟨d, hdD⟩ := hDnonempty
    refine ⟨d, Finset.mem_sdiff.2 ⟨hDsub hdD, ?_⟩⟩
    intro hds
    exact (Finset.mem_sdiff.1 (hsSubResidual hds)).2 hdD
  obtain ⟨e, heG, hes, heOutside⟩ :=
    hconn s hsSub hsNonempty hcomplementNonempty
  have heD : ¬Disjoint (G.ends e) D := by
    intro heDisjointD
    have heResidual : e ∈ (G.deleteVertices D).edges :=
      (mem_deleteVertices_edges_iff G D e).2 ⟨heG, heDisjointD⟩
    have heEqS : G.ends e = s :=
      hsInfo.2.2.1.2 e heResidual hes
    rw [heEqS, Finset.not_disjoint_iff] at heOutside
    obtain ⟨v, hvs, hvOutside⟩ := heOutside
    exact (Finset.mem_sdiff.1 hvOutside).2 hvs
  have heResidualSide : ¬Disjoint (G.ends e) (G.vertices \ D) := by
    rw [Finset.not_disjoint_iff] at hes ⊢
    obtain ⟨v, hve, hvs⟩ := hes
    exact ⟨v, hve, hsSubResidual hvs⟩
  exact ⟨e, (mem_boundaryEdges_iff G D e).2
    ⟨heG, heD, heResidualSide⟩, hes⟩

theorem doubleComponentCount_deleteVertices_le_crossingDeletedEdges_of_cutConnected
    (G : LabeledMultigraph V E) (D : Finset V)
    (hconn : G.CutConnected) (hDsub : D ⊆ G.vertices)
    (hDnonempty : D.Nonempty) :
    (G.deleteVertices D).doubleComponentCount ≤
      (G.boundaryEdges D).card :=
  doubleComponentCount_deleteVertices_le_crossingDeletedEdges G D
    (deletionWitnessed_of_cutConnected G D hconn hDsub hDnonempty)

/-- Deleted and retained edge labels partition the original labels. -/
theorem edgeCount_delete_add_crossingDeletedEdges_card
    (G : LabeledMultigraph V E) (D : Finset V) :
    (G.deleteVertices D).edgeCount + (G.crossingDeletedEdges D).card =
      G.edgeCount := by
  exact Finset.card_filter_add_card_filter_not
    (fun e ↦ Disjoint (G.ends e) D)

theorem crossingDeletedEdges_singleton_eq
    (G : LabeledMultigraph V E) (x : V) :
    G.crossingDeletedEdges {x} = G.incidentEdges x := by
  ext e
  simp [crossingDeletedEdges, incidentEdges, Finset.disjoint_singleton_right]

theorem crossingDeletedEdges_pair_eq
    (G : LabeledMultigraph V E) (x y : V) :
    G.crossingDeletedEdges {x, y} = G.incidentEdges x ∪ G.incidentEdges y := by
  classical
  ext e
  simp only [mem_crossingDeletedEdges_iff, Finset.mem_union, mem_incidentEdges_iff]
  have hdis : Disjoint (G.ends e) {x, y} ↔ x ∉ G.ends e ∧ y ∉ G.ends e := by
    simp
  rw [hdis]
  tauto

/-- Unlike the boundary, deletion counts each internal edge once. -/
theorem edgeCount_delete_pair_add_degrees
    (G : LabeledMultigraph V E) (x y : V) :
    (G.deleteVertices {x, y}).edgeCount + G.degree x + G.degree y =
      G.edgeCount + G.multiplicity x y := by
  have h := edgeCount_delete_add_crossingDeletedEdges_card G {x, y}
  rw [crossingDeletedEdges_pair_eq] at h
  have hc := Finset.card_union_add_card_inter (G.incidentEdges x) (G.incidentEdges y)
  rw [← edgesBetween_eq_inter_incidentEdges] at hc
  change (G.incidentEdges x ∪ G.incidentEdges y).card + G.multiplicity x y =
    G.degree x + G.degree y at hc
  omega

theorem edgeCount_delete_singleton_add_degree
    (G : LabeledMultigraph V E) (x : V) :
    (G.deleteVertices {x}).edgeCount + G.degree x = G.edgeCount := by
  have h := edgeCount_delete_add_crossingDeletedEdges_card G {x}
  rw [crossingDeletedEdges_singleton_eq] at h
  exact h

theorem vertexCount_delete_singleton_add_one
    (G : LabeledMultigraph V E) {x : V} (hx : x ∈ G.vertices) :
    (G.deleteVertices {x}).vertexCount + 1 = G.vertexCount := by
  have hsub : ({x} : Finset V) ⊆ G.vertices := by simpa using hx
  simpa only [vertexCount, deleteVertices, Finset.card_singleton] using
    Finset.card_sdiff_add_card_eq_card hsub

theorem vertexCount_delete_pair_add_two
    (G : LabeledMultigraph V E) {x y : V}
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) (hxy : x ≠ y) :
    (G.deleteVertices {x, y}).vertexCount + 2 = G.vertexCount := by
  have hsub : ({x, y} : Finset V) ⊆ G.vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx, hy⟩
  have h := Finset.card_sdiff_add_card_eq_card hsub
  simpa [vertexCount, deleteVertices, hxy] using h

theorem doubleComponentCount_delete_singleton_le_degree
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x : V} (hx : x ∈ G.vertices) :
    (G.deleteVertices {x}).doubleComponentCount ≤ G.degree x := by
  have h := doubleComponentCount_deleteVertices_le_crossingDeletedEdges_of_cutConnected
    G {x} hconn (by simpa using hx) (by simp)
  simpa only [boundaryEdges_singleton_card G hx] using h

/-- Exact exceptional-component budget in the two-vertex branch. -/
theorem doubleComponentCount_delete_pair_add_twice_multiplicity_le
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices) (hy : y ∈ G.vertices)
    (hxy : x ≠ y) :
    (G.deleteVertices {x, y}).doubleComponentCount + 2 * G.multiplicity x y ≤
      G.degree x + G.degree y := by
  have hsub : ({x, y} : Finset V) ⊆ G.vertices := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hx, hy⟩
  have h := doubleComponentCount_deleteVertices_le_crossingDeletedEdges_of_cutConnected
    G {x, y} hconn hsub (by simp)
  have hcard := boundaryEdges_pair_card_add_twice_multiplicity G hxy
  omega

/-- A connected graph with at least three active vertices has no isolated
double component. -/
theorem doubleComponentCount_eq_zero_of_cutConnected
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    (hv : 3 ≤ G.vertexCount) : G.doubleComponentCount = 0 := by
  classical
  unfold doubleComponentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hs' := (mem_doubleComponents_iff G s).1 hs
  have hsNonempty : s.Nonempty := by
    rw [← Finset.card_pos, hs'.2.1]
    norm_num
  have hcomp : (G.vertices \ s).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hs'.1, hs'.2.1]
    change 0 < G.vertexCount - 2
    omega
  obtain ⟨e, he, hes, heout⟩ := hconn s hs'.1 hsNonempty hcomp
  have heq := hs'.2.2.1.2 e he hes
  rw [heq, Finset.not_disjoint_iff] at heout
  obtain ⟨v, hvs, hvout⟩ := heout
  exact (Finset.mem_sdiff.1 hvout).2 hvs

/-- Every vertex of an isolated double component has weighted degree two. -/
theorem degree_eq_two_of_mem_doubleComponent
    (G : LabeledMultigraph V E) {s : Finset V}
    (hs : G.IsDoubleComponent s) {v : V} (hv : v ∈ s) :
    G.degree v = 2 := by
  have heq : G.incidentEdges v = G.edgesOn s := by
    ext e
    constructor
    · intro he
      have he' := (mem_incidentEdges_iff G v e).1 he
      have hmeet : ¬Disjoint (G.ends e) s := by
        rw [Finset.not_disjoint_iff]
        exact ⟨v, he'.2, hv⟩
      exact Finset.mem_filter.2 ⟨he'.1, hs.2.1.2 e he'.1 hmeet⟩
    · intro he
      have he' : e ∈ G.edges ∧ G.ends e = s := Finset.mem_filter.1 he
      exact (mem_incidentEdges_iff G v e).2 ⟨he'.1, he'.2.symm ▸ hv⟩
  unfold degree
  rw [heq]
  exact hs.2.2

/-- The remaining incident labels at y are exactly those not incident to x. -/
theorem incidentEdges_delete_singleton_eq
    (G : LabeledMultigraph V E) (x y : V) :
    (G.deleteVertices {x}).incidentEdges y =
      G.incidentEdges y \ G.incidentEdges x := by
  ext e
  simp only [mem_incidentEdges_iff, mem_deleteVertices_edges_iff,
    Finset.disjoint_singleton_right, Finset.mem_sdiff]
  change ((e ∈ G.edges ∧ x ∉ G.ends e) ∧ y ∈ G.ends e) ↔
    ((e ∈ G.edges ∧ y ∈ G.ends e) ∧ ¬(e ∈ G.edges ∧ x ∈ G.ends e))
  tauto

theorem degree_delete_singleton_add_multiplicity
    (G : LabeledMultigraph V E) (x y : V) :
    (G.deleteVertices {x}).degree y + G.multiplicity x y = G.degree y := by
  unfold degree multiplicity
  rw [incidentEdges_delete_singleton_eq, edgesBetween_eq_inter_incidentEdges,
    Finset.inter_comm (G.incidentEdges x)]
  exact Finset.card_sdiff_add_card_inter _ _

/-- A degree-two neighbor joined by one edge cannot belong to an exceptional
component after singleton deletion: its remaining degree is one. -/
theorem not_mem_doubleComponent_after_delete_of_degree_two
    (G : LabeledMultigraph V E) {x y : V}
    (hy : G.degree y = 2) (hxy : G.multiplicity x y = 1)
    {s : Finset V} (hs : (G.deleteVertices {x}).IsDoubleComponent s) :
    y ∉ s := by
  intro hys
  have hdegree := degree_eq_two_of_mem_doubleComponent _ hs hys
  have hsum := degree_delete_singleton_add_multiplicity G x y
  omega

/-- If x has only the neighbor y, every residual double component contains y. -/
theorem mem_doubleComponent_of_unique_neighbor
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices)
    (hneighbor : ∀ e ∈ G.incidentEdges x, G.ends e = {x, y})
    {s : Finset V} (hs : s ∈ (G.deleteVertices {x}).doubleComponents) :
    y ∈ s := by
  have hw := deletionWitnessed_of_cutConnected G {x} hconn
    (by simpa using hx) (by simp)
  obtain ⟨e, he, hes⟩ := hw s hs
  have heInc : e ∈ G.incidentEdges x := by
    rw [← boundaryEdges_singleton_eq_incidentEdges G hx]
    exact he
  have heEnds := hneighbor e heInc
  rw [heEnds, Finset.not_disjoint_iff] at hes
  obtain ⟨v, hvPair, hvs⟩ := hes
  have hvCases : v = x ∨ v = y := by simpa using hvPair
  rcases hvCases with hvx | hvy
  · have hsSub := (mem_doubleComponents_iff _ s).1 hs |>.1
    have hvNotX := (Finset.mem_sdiff.1 (hsSub hvs)).2
    exact False.elim (hvNotX (by simp [hvx]))
  · exact hvy ▸ hvs

theorem doubleComponentCount_delete_le_one_of_unique_neighbor
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices)
    (hneighbor : ∀ e ∈ G.incidentEdges x, G.ends e = {x, y}) :
    (G.deleteVertices {x}).doubleComponentCount ≤ 1 := by
  classical
  unfold doubleComponentCount
  apply Finset.card_le_one.mpr
  intro s hs t ht
  by_contra hst
  have hdis := disjoint_of_isDoubleComponent (G.deleteVertices {x})
    ((mem_doubleComponents_iff _ s).1 hs).2
    ((mem_doubleComponents_iff _ t).1 ht).2 hst
  rw [Finset.disjoint_left] at hdis
  exact hdis (mem_doubleComponent_of_unique_neighbor G hconn hx hneighbor hs)
    (mem_doubleComponent_of_unique_neighbor G hconn hx hneighbor ht)

theorem doubleComponentCount_delete_eq_zero_of_unique_degree_two_neighbor
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x y : V} (hx : x ∈ G.vertices)
    (hneighbor : ∀ e ∈ G.incidentEdges x, G.ends e = {x, y})
    (hy : G.degree y = 2) (hxy : G.multiplicity x y = 1) :
    (G.deleteVertices {x}).doubleComponentCount = 0 := by
  classical
  unfold doubleComponentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  exact not_mem_doubleComponent_after_delete_of_degree_two G hy hxy
    ((mem_doubleComponents_iff _ s).1 hs).2
    (mem_doubleComponent_of_unique_neighbor G hconn hx hneighbor hs)

/-- Disjoint exceptional components can be charged to distinct vertices in
any set meeting every component. -/
theorem doubleComponentCount_le_card_of_vertex_witness
    (G : LabeledMultigraph V E) (B : Finset V)
    (hw : ∀ s ∈ G.doubleComponents, ∃ y ∈ B, y ∈ s) :
    G.doubleComponentCount ≤ B.card := by
  classical
  let pick : ↥G.doubleComponents → ↥B := fun s ↦
    ⟨Classical.choose (hw s.1 s.2), (Classical.choose_spec (hw s.1 s.2)).1⟩
  have hinj : Function.Injective pick := by
    intro s t heq
    apply Subtype.ext
    by_contra hst
    have hd := disjoint_of_isDoubleComponent G
      ((mem_doubleComponents_iff G s.1).1 s.2).2
      ((mem_doubleComponents_iff G t.1).1 t.2).2 hst
    have hs : (pick s).1 ∈ s.1 := (Classical.choose_spec (hw s.1 s.2)).2
    have ht : (pick t).1 ∈ t.1 := (Classical.choose_spec (hw t.1 t.2)).2
    have he : (pick s).1 = (pick t).1 := congrArg Subtype.val heq
    rw [← he] at ht
    exact (Finset.disjoint_left.1 hd) hs ht
  simpa only [doubleComponentCount, Fintype.card_coe] using
    Fintype.card_le_of_injective pick hinj

def eligibleNeighbors (G : LabeledMultigraph V E) (x : V) : Finset V :=
  G.vertices.filter fun y ↦ y ≠ x ∧ 0 < G.multiplicity x y ∧ 3 ≤ G.degree y

/-- A residual double component must contain a neighbor with original
degree at least three. This remains true with parallel labels. -/
theorem exists_eligibleNeighbor_in_doubleComponent
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x : V} (hx : x ∈ G.vertices)
    {s : Finset V} (hs : s ∈ (G.deleteVertices {x}).doubleComponents) :
    ∃ y ∈ G.eligibleNeighbors x, y ∈ s := by
  classical
  have hw := deletionWitnessed_of_cutConnected G {x} hconn
    (by simpa using hx) (by simp)
  obtain ⟨e, he, hes⟩ := hw s hs
  have heInc : e ∈ G.incidentEdges x := by
    rw [← boundaryEdges_singleton_eq_incidentEdges G hx]
    exact he
  have he' := (mem_incidentEdges_iff G x e).1 heInc
  rw [Finset.not_disjoint_iff] at hes
  obtain ⟨y, hye, hys⟩ := hes
  have hyNe : y ≠ x := by
    have hyResidual := (mem_doubleComponents_iff _ s).1 hs |>.1 hys
    have hyNot := (Finset.mem_sdiff.1 hyResidual).2
    simpa only [Finset.mem_singleton] using hyNot
  have hyV : y ∈ G.vertices := G.ends_subset e he'.1 hye
  have hmult : 0 < G.multiplicity x y := by
    apply Finset.card_pos.mpr
    exact ⟨e, (mem_edgesBetween_iff G x y e).2 ⟨he'.1, he'.2, hye⟩⟩
  have hyTwo := degree_eq_two_of_mem_doubleComponent (G.deleteVertices {x})
    ((mem_doubleComponents_iff _ s).1 hs).2 hys
  have hsum := degree_delete_singleton_add_multiplicity G x y
  have hyThree : 3 ≤ G.degree y := by omega
  exact ⟨y, Finset.mem_filter.2 ⟨hyV, hyNe, hmult, hyThree⟩, hys⟩

/-- This supplies q_x <= t in the degree-two/two-neighbor branch, where t
counts the neighbors of original weighted degree at least three. -/
theorem doubleComponentCount_delete_le_eligibleNeighbors_card
    (G : LabeledMultigraph V E) (hconn : G.CutConnected)
    {x : V} (hx : x ∈ G.vertices) :
    (G.deleteVertices {x}).doubleComponentCount ≤ (G.eligibleNeighbors x).card :=
  doubleComponentCount_le_card_of_vertex_witness _ _
    (fun _ hs ↦ exists_eligibleNeighbor_in_doubleComponent G hconn hx hs)

/-- A weighted degree-one vertex has a unique neighbor and multiplicity one;
the structural hypothesis used above is derived here from the degree. -/
theorem exists_unique_neighbor_of_degree_one
    (G : LabeledMultigraph V E) {x : V} (hd : G.degree x = 1) :
    ∃ y ∈ G.vertices, x ≠ y ∧ G.multiplicity x y = 1 ∧
      ∀ e ∈ G.incidentEdges x, G.ends e = {x, y} := by
  classical
  obtain ⟨e, hsingle⟩ := Finset.card_eq_one.mp hd
  have heInc : e ∈ G.incidentEdges x := by simp [hsingle]
  have he := (mem_incidentEdges_iff G x e).1 heInc
  have hcard : ((G.ends e).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem he.2, G.ends_card e he.1]
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < ((G.ends e).erase x).card by omega)
  have hyEnds := Finset.mem_of_mem_erase hy
  have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  have hends := ends_eq_pair_of_both_mem G he.1 hxy he.2 hyEnds
  have hbetween : G.edgesBetween x y = {e} := by
    ext f
    constructor
    · intro hf
      have hf' := (mem_edgesBetween_iff G x y f).1 hf
      have hfInc := (mem_incidentEdges_iff G x f).2 ⟨hf'.1, hf'.2.1⟩
      simpa only [hsingle] using hfInc
    · intro hf
      have hfe : f = e := Finset.mem_singleton.mp hf
      subst f
      exact (mem_edgesBetween_iff G x y e).2 ⟨he.1, he.2, hyEnds⟩
  refine ⟨y, G.ends_subset e he.1 hyEnds, hxy, ?_, ?_⟩
  · simp [multiplicity, hbetween]
  · intro f hf
    have hfe : f = e := by simpa [hsingle] using hf
    simpa [hfe] using hends

/-- Pure-integer form of the sharp multigraph inequality.  It is the fourth
power of `Z(G) ≤ 2^((v+2e)/4) Γ^q` with
`Γ = 3/(2*sqrt 2)`. -/
def SharpBound (G : LabeledMultigraph V E) : Prop :=
  64 ^ G.doubleComponentCount * G.matchingCount ^ 4 ≤
    2 ^ (G.vertexCount + 2 * G.edgeCount) *
      81 ^ G.doubleComponentCount

end LabeledMultigraph

end StableMatchingsE2E
