import StableMatchings355.FiniteJoin
import StableMatchings355.Interval

namespace StableMatchings355

/-! The finite, end-to-end support-window bridge used by the reveal argument.
The ranked table is exact: every entry is realized by a stable matching and
every stable partner of the target man occurs in the table. -/

structure ExactStablePartnerEnumeration {n q : Nat}
    (P : Profile (Fin n) (Fin n)) (m : Fin n) where
  ranked : RankedPartners P m q
  realized : forall i, Exists fun sigma : Matching (Fin n) (Fin n) =>
    Stable P sigma /\ sigma.manPartner m = ranked.partner i
  complete : forall mu : Matching (Fin n) (Fin n), Stable P mu ->
    Exists fun i : Fin q => mu.manPartner m = ranked.partner i

def CompatibleOn {n : Nat} (P : Profile (Fin n) (Fin n))
    (base nu : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop) : Prop :=
  Stable P nu /\ forall p, revealed p -> nu.manPartner p = base.manPartner p

def lowerBoundary {n q : Nat} : Option (Fin q × Fin n) -> Nat
  | none => 0
  | some hp => hp.1.val + 1

def upperBoundary {n q : Nat} : Option (Fin q × Fin n) -> Nat
  | none => q
  | some hp => hp.1.val

def IsRevealedMarker {n q : Nat} {P : Profile (Fin n) (Fin n)}
    {m : Fin n} (E : ExactStablePartnerEnumeration (q := q) P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    (h : Fin q) (p : Fin n) : Prop :=
  revealed p /\ base.manPartner p = E.ranked.partner h

/- The option values encode real nearest markers, while `none` encodes the
absence of a marker on that side.  The maximal/minimal fields certify that
the chosen real markers really are nearest; the `none` fields certify the
sentinels rather than silently assuming an endpoint marker exists. -/
structure NearestRevealedWindow {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    (j : Fin q) where
  lower : Option (Fin q × Fin n)
  upper : Option (Fin q × Fin n)
  lower_valid : forall h p, lower = some (h, p) ->
    IsRevealedMarker E base revealed h p /\ h.val < j.val
  upper_valid : forall h p, upper = some (h, p) ->
    IsRevealedMarker E base revealed h p /\ j.val < h.val
  lower_none : lower = none -> forall h p,
    IsRevealedMarker E base revealed h p -> Not (h.val < j.val)
  upper_none : upper = none -> forall h p,
    IsRevealedMarker E base revealed h p -> Not (j.val < h.val)
  lower_maximal : forall h p, lower = some (h, p) -> forall h' p',
    IsRevealedMarker E base revealed h' p' -> h'.val < j.val -> h'.val <= h.val
  upper_minimal : forall h p, upper = some (h, p) -> forall h' p',
    IsRevealedMarker E base revealed h' p' -> j.val < h'.val -> h.val <= h'.val

private theorem exists_maximal_below {R : Nat -> Prop} (B : Nat)
    (hex : Exists R) (hbound : forall k, R k -> k < B) :
    Exists fun k => R k /\ forall l, R l -> l <= k := by
  induction B generalizing R with
  | zero =>
      obtain ⟨k, hk⟩ := hex
      exact False.elim (Nat.not_lt_zero k (hbound k hk))
  | succ B ih =>
      classical
      by_cases htop : R B
      · exact ⟨B, htop, by
          intro l hl
          have := hbound l hl
          omega⟩
      · apply ih hex
        intro k hk
        have hlt := hbound k hk
        have hne : k ≠ B := by
          intro he
          apply htop
          simpa [he] using hk
        omega

private theorem exists_minimal_below {R : Nat -> Prop} (B : Nat)
    (hex : Exists R) (hbound : forall k, R k -> k < B) :
    Exists fun k => R k /\ forall l, R l -> k <= l := by
  induction B generalizing R with
  | zero =>
      obtain ⟨k, hk⟩ := hex
      exact False.elim (Nat.not_lt_zero k (hbound k hk))
  | succ B ih =>
      classical
      by_cases hzero : R 0
      · exact ⟨0, hzero, by intro l hl; omega⟩
      · have hex' : Exists fun k => R (k + 1) := by
          obtain ⟨l, hl⟩ := hex
          have hlpos : 0 < l := by
            have hlne : l ≠ 0 := by
              intro he
              apply hzero
              simpa [he] using hl
            omega
          refine ⟨l - 1, ?_⟩
          have he : l - 1 + 1 = l := by omega
          rw [he]
          exact hl
        have hbound' : forall k, R (k + 1) -> k < B := by
          intro k hk
          have := hbound (k + 1) hk
          omega
        obtain ⟨k, hk, hmin⟩ := ih hex' hbound'
        refine ⟨k + 1, hk, ?_⟩
        intro l hl
        have hlpos : 0 < l := by
          have hlne : l ≠ 0 := by
            intro he
            apply hzero
            simpa [he] using hl
          omega
        have he : l - 1 + 1 = l := by omega
        have hp := hmin (l - 1) (by rw [he]; exact hl)
        omega

theorem exists_nearestRevealedWindow {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    (j : Fin q) : Nonempty (NearestRevealedWindow E base revealed j) := by
  classical
  let LowerOK := fun lower : Option (Fin q × Fin n) =>
    (forall h p, lower = some (h, p) ->
      IsRevealedMarker E base revealed h p /\ h.val < j.val) /\
    (lower = none -> forall h p,
      IsRevealedMarker E base revealed h p -> Not (h.val < j.val)) /\
    (forall h p, lower = some (h, p) -> forall h' p',
      IsRevealedMarker E base revealed h' p' -> h'.val < j.val -> h'.val <= h.val)
  let UpperOK := fun upper : Option (Fin q × Fin n) =>
    (forall h p, upper = some (h, p) ->
      IsRevealedMarker E base revealed h p /\ j.val < h.val) /\
    (upper = none -> forall h p,
      IsRevealedMarker E base revealed h p -> Not (j.val < h.val)) /\
    (forall h p, upper = some (h, p) -> forall h' p',
      IsRevealedMarker E base revealed h' p' -> j.val < h'.val -> h.val <= h'.val)
  have hLower : Exists LowerOK := by
    by_cases hex : Exists fun hp : Fin q × Fin n =>
        IsRevealedMarker E base revealed hp.1 hp.2 /\ hp.1.val < j.val
    · let R := fun k : Nat => Exists fun hp : Fin q × Fin n =>
          IsRevealedMarker E base revealed hp.1 hp.2 /\
          hp.1.val < j.val /\ hp.1.val = k
      have hR : Exists R := by
        obtain ⟨⟨h, p⟩, hm, hlt⟩ := hex
        exact ⟨h.val, ⟨(h, p), hm, hlt, rfl⟩⟩
      obtain ⟨k, ⟨⟨h, p⟩, hm, hlt, hk⟩, hmax⟩ :=
        exists_maximal_below j.val hR (by
          intro x hx
          obtain ⟨hp, hm, hlt, he⟩ := hx
          simpa [← he] using hlt)
      refine ⟨some (h, p), ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro h' p' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨hm, hlt⟩
      · intro he
        simp at he
      · intro h' p' he h'' p'' hm'' hlt''
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hx : R h''.val := ⟨(h'', p''), hm'', hlt'', rfl⟩
        have := hmax h''.val hx
        exact Nat.le_trans this (Nat.le_of_eq hk.symm)
    · refine ⟨none, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro h p he
        simp at he
      · intro he h p hm hlt
        exact hex ⟨(h, p), hm, hlt⟩
      · intro h p he
        simp at he
  have hUpper : Exists UpperOK := by
    by_cases hex : Exists fun hp : Fin q × Fin n =>
        IsRevealedMarker E base revealed hp.1 hp.2 /\ j.val < hp.1.val
    · let R := fun k : Nat => Exists fun hp : Fin q × Fin n =>
          IsRevealedMarker E base revealed hp.1 hp.2 /\
          j.val < hp.1.val /\ hp.1.val = k
      have hR : Exists R := by
        obtain ⟨⟨h, p⟩, hm, hlt⟩ := hex
        exact ⟨h.val, ⟨(h, p), hm, hlt, rfl⟩⟩
      obtain ⟨k, ⟨⟨h, p⟩, hm, hlt, hk⟩, hmin⟩ :=
        exists_minimal_below q hR (by
          intro x hx
          obtain ⟨hp, hm, hlt, he⟩ := hx
          simpa [← he] using hp.1.isLt)
      refine ⟨some (h, p), ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro h' p' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨hm, hlt⟩
      · intro he
        simp at he
      · intro h' p' he h'' p'' hm'' hlt''
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hx : R h''.val := ⟨(h'', p''), hm'', hlt'', rfl⟩
        have := hmin h''.val hx
        exact Nat.le_trans (Nat.le_of_eq hk) this
    · refine ⟨none, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · intro h p he
        simp at he
      · intro he h p hm hlt
        exact hex ⟨(h, p), hm, hlt⟩
      · intro h p he
        simp at he
  obtain ⟨lower, hlv, hln, hlm⟩ := hLower
  obtain ⟨upper, huv, hun, hum⟩ := hUpper
  exact ⟨{
    lower := lower
    upper := upper
    lower_valid := hlv
    upper_valid := huv
    lower_none := hln
    upper_none := hun
    lower_maximal := hlm
    upper_minimal := hum
  }⟩

theorem actual_index_in_nearest_window {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {m : Fin n}
    {E : ExactStablePartnerEnumeration P m}
    {base : Matching (Fin n) (Fin n)} {revealed : Fin n -> Prop} {j : Fin q}
    (W : NearestRevealedWindow E base revealed j) :
    lowerBoundary W.lower <= j.val /\ j.val < upperBoundary W.upper := by
  constructor
  · cases h : W.lower with
    | none => simp [lowerBoundary]
    | some hp =>
        rcases hp with ⟨i, p⟩
        have hi := (W.lower_valid i p h).2
        simp only [lowerBoundary]
        omega
  · cases h : W.upper with
    | none => simpa [upperBoundary] using j.isLt
    | some hp =>
        rcases hp with ⟨i, p⟩
        exact (W.upper_valid i p h).2

/- `none` is the left sentinel immediately before index zero.  A real lower
marker at `h` moves the inclusive lower endpoint to `h+1`. -/
theorem lower_marker_forces_index {n q : Nat} (P : Profile (Fin n) (Fin n))
    {m : Fin n} (E : ExactStablePartnerEnumeration P m)
    (base nu : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j t : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (hcompat : CompatibleOn P base nu revealed)
    (hnuTarget : nu.manPartner m = E.ranked.partner t)
    (lower : Option (Fin q × Fin n))
    (hlower : forall h p, lower = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ h.val < j.val) :
    lowerBoundary lower <= t.val := by
  cases lower with
  | none => simp [lowerBoundary]
  | some hp =>
      rcases hp with ⟨h, p⟩
      obtain ⟨hrev, hbaseReveal, hhj⟩ := hlower h p rfl
      obtain ⟨sigma, hsigma, hsigmaPair⟩ := E.realized h
      have hnuReveal : nu.manPartner p = E.ranked.partner h := by
        calc
          nu.manPartner p = base.manPartner p := hcompat.2 p hrev
          _ = E.ranked.partner h := hbaseReveal
      have hlt : h.val < t.val :=
        revealed_lower_barrier P (finite_hasMenJoin n P) E.ranked sigma base nu
          hsigma hbase hcompat.1 hsigmaPair hbaseTarget hnuTarget
          hbaseReveal hnuReveal hhj
      simp only [lowerBoundary]
      omega

/- `none` is the right sentinel immediately after index `q-1`.  A real upper
marker at `h` makes `h` the exclusive upper endpoint. -/
theorem upper_marker_forces_index {n q : Nat} (P : Profile (Fin n) (Fin n))
    {m : Fin n} (E : ExactStablePartnerEnumeration P m)
    (base nu : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j t : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (hcompat : CompatibleOn P base nu revealed)
    (hnuTarget : nu.manPartner m = E.ranked.partner t)
    (upper : Option (Fin q × Fin n))
    (hupper : forall h p, upper = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ j.val < h.val) :
    t.val < upperBoundary upper := by
  cases upper with
  | none => simpa [upperBoundary] using t.isLt
  | some hp =>
      rcases hp with ⟨h, p⟩
      obtain ⟨hrev, hbaseReveal, hjh⟩ := hupper h p rfl
      obtain ⟨sigma, hsigma, hsigmaPair⟩ := E.realized h
      have hnuReveal : nu.manPartner p = E.ranked.partner h := by
        calc
          nu.manPartner p = base.manPartner p := hcompat.2 p hrev
          _ = E.ranked.partner h := hbaseReveal
      exact revealed_upper_barrier P (finite_hasMenJoin n P) E.ranked sigma base nu
        hsigma hbase hcompat.1 hsigmaPair hbaseTarget hnuTarget
        hbaseReveal hnuReveal hjh

theorem compatible_index_in_revealed_window {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base nu : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j t : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (hcompat : CompatibleOn P base nu revealed)
    (hnuTarget : nu.manPartner m = E.ranked.partner t)
    (lower upper : Option (Fin q × Fin n))
    (hlower : forall h p, lower = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ h.val < j.val)
    (hupper : forall h p, upper = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ j.val < h.val) :
    lowerBoundary lower <= t.val /\ t.val < upperBoundary upper := by
  exact ⟨lower_marker_forces_index P E base nu revealed hbase hbaseTarget hcompat
      hnuTarget lower hlower,
    upper_marker_forces_index P E base nu revealed hbase hbaseTarget hcompat
      hnuTarget upper hupper⟩

/- The requested nearest-marker formulation.  Containment is derived from
stable-pair sidedness; nearestness only certifies that this is the tight
window determined by all revealed owners. -/
theorem compatible_index_in_nearest_revealed_window {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base nu : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j t : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (hcompat : CompatibleOn P base nu revealed)
    (hnuTarget : nu.manPartner m = E.ranked.partner t)
    (W : NearestRevealedWindow E base revealed j) :
    lowerBoundary W.lower <= t.val /\ t.val < upperBoundary W.upper := by
  apply compatible_index_in_revealed_window P E base nu revealed hbase
    hbaseTarget hcompat hnuTarget W.lower W.upper
  · intro h p he
    obtain ⟨hm, hlt⟩ := W.lower_valid h p he
    exact ⟨hm.1, hm.2, hlt⟩
  · intro h p he
    obtain ⟨hm, hlt⟩ := W.upper_valid h p he
    exact ⟨hm.1, hm.2, hlt⟩

private theorem length_le_of_nodup_subset {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} (hnd : xs.Nodup) (hsub : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnd
      have ha : a ∈ ys := hsub (by simp)
      have htail : xs ⊆ ys.erase a := by
        intro b hb
        have hba : b ≠ a := by
          intro e
          apply hnd.1
          simpa [e] using hb
        exact (List.mem_erase_of_ne hba).2 (hsub (by simp [hb]))
      have hle := ih hnd.2 htail
      rw [List.length_erase_of_mem ha] at hle
      have hy : 0 < ys.length := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

private theorem nodup_map_of_injOn {α β : Type} {f : α -> β} {xs : List α}
    (hnd : xs.Nodup)
    (hinj : forall a, a ∈ xs -> forall b, b ∈ xs -> f a = f b -> a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨b, hb, hfb⟩ := hmem
        have hab : a = b := hinj a (by simp) b (by simp [hb]) hfb.symm
        exact hnd.1 (by simpa [hab] using hb)
      · apply ih hnd.2
        intro b hb c hc hbc
        exact hinj b (by simp [hb]) c (by simp [hc]) hbc

/- A purely finite cardinality lemma.  It deliberately uses lists rather than
`Finset`, so the project remains dependency-free (`Std` only). -/
theorem nodup_window_length_le {q lo hi : Nat} (support : List (Fin q))
    (hnd : support.Nodup)
    (hwindow : forall t, t ∈ support -> lo <= t.val /\ t.val < hi) :
    support.length <= hi - lo := by
  let shifted := support.map fun t => t.val - lo
  have hndShifted : shifted.Nodup := by
    apply nodup_map_of_injOn hnd
    intro a ha b hb hab
    apply Fin.eq_of_val_eq
    have haw := (hwindow a ha).1
    have hbw := (hwindow b hb).1
    omega
  have hsub : shifted ⊆ List.range (hi - lo) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [List.mem_range]
    obtain ⟨hlt, htu⟩ := hwindow t ht
    omega
  have hle := length_le_of_nodup_subset hndShifted hsub
  simpa [shifted] using hle

/- Any duplicate-free list of indices that is witnessed by conditionally
compatible stable matchings has size at most the revealed window length. -/
theorem compatible_support_length_le {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (lower upper : Option (Fin q × Fin n))
    (hlower : forall h p, lower = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ h.val < j.val)
    (hupper : forall h p, upper = some (h, p) ->
      revealed p /\ base.manPartner p = E.ranked.partner h /\ j.val < h.val)
    (support : List (Fin q)) (hnd : support.Nodup)
    (hwitness : forall t, t ∈ support ->
      Exists fun nu : Matching (Fin n) (Fin n) =>
        CompatibleOn P base nu revealed /\
        nu.manPartner m = E.ranked.partner t) :
    support.length <= upperBoundary upper - lowerBoundary lower := by
  apply nodup_window_length_le support hnd
  intro t ht
  obtain ⟨nu, hcompat, htarget⟩ := hwitness t ht
  exact compatible_index_in_revealed_window P E base nu revealed hbase
    hbaseTarget hcompat htarget lower upper hlower hupper

theorem nearest_compatible_support_length_le {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (W : NearestRevealedWindow E base revealed j)
    (support : List (Fin q)) (hnd : support.Nodup)
    (hwitness : forall t, t ∈ support ->
      Exists fun nu : Matching (Fin n) (Fin n) =>
        CompatibleOn P base nu revealed /\
        nu.manPartner m = E.ranked.partner t) :
    support.length <= upperBoundary W.upper - lowerBoundary W.lower := by
  apply compatible_support_length_le P E base revealed hbase hbaseTarget
    W.lower W.upper _ _ support hnd hwitness
  · intro h p he
    obtain ⟨hm, hlt⟩ := W.lower_valid h p he
    exact ⟨hm.1, hm.2, hlt⟩
  · intro h p he
    obtain ⟨hm, hlt⟩ := W.upper_valid h p he
    exact ⟨hm.1, hm.2, hlt⟩

/- An explicit exact enumeration of the conditional index support.  The
`complete` field rules out interpreting `indices` as merely a convenient
subset of compatible choices. -/
structure ExactConditionalIndexSupport {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop) where
  indices : List (Fin q)
  nodup : indices.Nodup
  sound : forall t, t ∈ indices ->
    Exists fun nu : Matching (Fin n) (Fin n) =>
      CompatibleOn P base nu revealed /\
      nu.manPartner m = E.ranked.partner t
  complete : forall nu : Matching (Fin n) (Fin n),
    CompatibleOn P base nu revealed -> forall t,
      nu.manPartner m = E.ranked.partner t -> t ∈ indices

private theorem nodup_ofFn_of_injective {α : Type} {n : Nat} (f : Fin n -> α)
    (hf : Function.Injective f) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have heq : i.succ = (0 : Fin (n + 1)) := hf hi
        have hval := congrArg Fin.val heq
        simp at hval
      · apply ih (fun i => f i.succ)
        intro i j hij
        apply Fin.eq_of_val_eq
        have hval := congrArg Fin.val (hf hij)
        simpa using hval

private theorem nodup_filter_bool {α : Type} {p : α -> Bool} {xs : List α}
    (hnd : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.filter]
      split
      · rw [List.nodup_cons]
        constructor
        · intro hm
          rw [List.mem_filter] at hm
          exact hnd.1 hm.1
        · exact ih hnd.2
      · exact ih hnd.2

private theorem get_injective_of_nodup {α : Type} (xs : List α)
    (hnd : xs.Nodup) : Function.Injective xs.get := by
  intro i j hij
  apply Fin.eq_of_val_eq
  apply Classical.byContradiction
  intro hne
  have hp := List.nodup_iff_pairwise_ne.mp hnd
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have hn := (List.pairwise_iff_getElem.mp hp) i.val j.val i.isLt j.isLt hlt
    apply hn
    simpa [List.get_eq_getElem] using hij
  · exact hne heq
  · have hn := (List.pairwise_iff_getElem.mp hp) j.val i.val j.isLt i.isLt hgt
    apply hn
    simpa [List.get_eq_getElem] using hij.symm

/- Every finite strict complete profile that has at least one stable matching
admits an exact, preference-ranked stable-partner enumeration.  The proof
filters all women by `StablePair` and merge-sorts the finite list by the
target man's weak preference. -/
theorem exists_exactStablePartnerEnumeration {n : Nat}
    (P : Profile (Fin n) (Fin n)) (m : Fin n) :
    Exists fun q => Nonempty (ExactStablePartnerEnumeration (q := q) P m) := by
  classical
  let StableW := fun w : Fin n => StablePair P m w
  let raw := (List.ofFn fun w : Fin n => w).filter fun w => decide (StableW w)
  let LePref := fun a b : Fin n => decide (a = b \/ P.manPref m a b)
  let sorted := raw.mergeSort LePref
  have hallNodup : (List.ofFn fun w : Fin n => w).Nodup :=
    nodup_ofFn_of_injective (fun w : Fin n => w) (fun _ _ h => h)
  have hrawNodup : raw.Nodup := nodup_filter_bool hallNodup
  have hsortedNodup : sorted.Nodup := by
    exact (List.mergeSort_perm raw LePref).symm.nodup hrawNodup
  have hLeTrans : forall a b c, LePref a b = true -> LePref b c = true ->
      LePref a c = true := by
    intro a b c hab hbc
    have hab' : a = b \/ P.manPref m a b := of_decide_eq_true hab
    have hbc' : b = c \/ P.manPref m b c := of_decide_eq_true hbc
    apply decide_eq_true
    rcases hab' with rfl | hab' <;> rcases hbc' with rfl | hbc'
    · exact Or.inl rfl
    · exact Or.inr hbc'
    · exact Or.inr hab'
    · exact Or.inr (P.man_trans m a b c hab' hbc')
  have hLeTotal : forall a b, (LePref a b || LePref b a) = true := by
    intro a b
    by_cases he : a = b
    · have hle : LePref a b = true := decide_eq_true (Or.inl he)
      simp [hle]
    · rcases P.man_total m a b he with hp | hp
      · have hle : LePref a b = true := decide_eq_true (Or.inr hp)
        simp [hle]
      · have hle : LePref b a = true := decide_eq_true (Or.inr hp)
        simp [hle]
  have hsorted : List.Pairwise (fun a b => LePref a b = true) sorted :=
    List.pairwise_mergeSort hLeTrans hLeTotal raw
  let partner := fun i : Fin sorted.length => sorted.get i
  have hpartnerInj : Function.Injective partner := get_injective_of_nodup sorted hsortedNodup
  have hrank : forall i j, P.manPref m (partner i) (partner j) <-> i.val < j.val := by
    intro i j
    constructor
    · intro hpref
      rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact hlt
      · have hij : i = j := Fin.eq_of_val_eq heq
        subst j
        exact False.elim ((P.man_asymm m _ _ hpref) hpref)
      · have hle := (List.pairwise_iff_getElem.mp hsorted)
            j.val i.val j.isLt i.isLt hgt
        have hle' : partner j = partner i \/ P.manPref m (partner j) (partner i) :=
          of_decide_eq_true (by simpa [LePref, partner, List.get_eq_getElem] using hle)
        rcases hle' with he | hrev
        · have : j = i := hpartnerInj he
          omega
        · exact False.elim ((P.man_asymm m _ _ hpref) hrev)
    · intro hij
      have hle := (List.pairwise_iff_getElem.mp hsorted)
          i.val j.val i.isLt j.isLt hij
      have hle' : partner i = partner j \/ P.manPref m (partner i) (partner j) :=
        of_decide_eq_true (by simpa [LePref, partner, List.get_eq_getElem] using hle)
      rcases hle' with he | hp
      · have : i = j := hpartnerInj he
        omega
      · exact hp
  refine ⟨sorted.length, ⟨{
    ranked := {
      partner := partner
      injective := hpartnerInj
      rank_spec := hrank
    }
    realized := ?_
    complete := ?_
  }⟩⟩
  · intro i
    have hm : partner i ∈ sorted := by
      exact sorted.get_mem i
    have hmraw : partner i ∈ raw := List.mem_mergeSort.mp hm
    rw [List.mem_filter] at hmraw
    have hsp : StableW (partner i) := of_decide_eq_true hmraw.2
    exact hsp
  · intro mu hmu
    let w := mu.manPartner m
    have hsp : StableW w := ⟨mu, hmu, rfl⟩
    have hwraw : w ∈ raw := by
      rw [List.mem_filter]
      constructor
      · rw [List.mem_ofFn]
        exact ⟨w, rfl⟩
      · exact decide_eq_true hsp
    have hwsorted : w ∈ sorted := List.mem_mergeSort.mpr hwraw
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hwsorted
    exact ⟨i, by simpa [w, partner] using hi.symm⟩

theorem exists_exactConditionalIndexSupport {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop) :
    Nonempty (ExactConditionalIndexSupport P E base revealed) := by
  classical
  let HasWitness := fun t : Fin q =>
    Exists fun nu : Matching (Fin n) (Fin n) =>
      CompatibleOn P base nu revealed /\
      nu.manPartner m = E.ranked.partner t
  let indices := (List.ofFn fun t : Fin q => t).filter fun t => decide (HasWitness t)
  refine ⟨{
    indices := indices
    nodup := ?_
    sound := ?_
    complete := ?_
  }⟩
  · apply nodup_filter_bool
    exact nodup_ofFn_of_injective (fun t : Fin q => t) (fun _ _ h => h)
  · intro t ht
    rw [List.mem_filter] at ht
    exact of_decide_eq_true ht.2
  · intro nu hcompat t htarget
    rw [List.mem_filter]
    constructor
    · rw [List.mem_ofFn]
      exact ⟨t, rfl⟩
    · exact decide_eq_true ⟨nu, hcompat, htarget⟩

theorem exact_conditional_support_length_le {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j)
    (W : NearestRevealedWindow E base revealed j)
    (S : ExactConditionalIndexSupport P E base revealed) :
    S.indices.length <= upperBoundary W.upper - lowerBoundary W.lower := by
  exact nearest_compatible_support_length_le P E base revealed hbase
    hbaseTarget W S.indices S.nodup S.sound

/- No window/support certificates are required from the caller: both exist
for the finite data and some exact support satisfies the certified bound. -/
theorem exists_exact_support_with_nearest_window_bound {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {m : Fin n}
    (E : ExactStablePartnerEnumeration P m)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    {j : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner m = E.ranked.partner j) :
    Exists fun W : NearestRevealedWindow E base revealed j =>
      Exists fun S : ExactConditionalIndexSupport P E base revealed =>
        S.indices.length <= upperBoundary W.upper - lowerBoundary W.lower := by
  obtain ⟨W⟩ := exists_nearestRevealedWindow E base revealed j
  obtain ⟨S⟩ := exists_exactConditionalIndexSupport P E base revealed
  exact ⟨W, S, exact_conditional_support_length_le P E base revealed hbase
    hbaseTarget W S⟩

/- Fully certificate-free finite bridge: an exact ranked stable-partner table,
the base index, nearest revealed window, and exact conditional support all
exist, and the support obeys the window bound. -/
theorem exists_full_conditional_support_bridge {n : Nat}
    (P : Profile (Fin n) (Fin n)) (m : Fin n)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n -> Prop)
    (hbase : Stable P base) :
    Exists fun q => Exists fun E : ExactStablePartnerEnumeration (q := q) P m =>
      Exists fun j : Fin q =>
        base.manPartner m = E.ranked.partner j /\
        Exists fun W : NearestRevealedWindow E base revealed j =>
          Exists fun S : ExactConditionalIndexSupport P E base revealed =>
            S.indices.length <= upperBoundary W.upper - lowerBoundary W.lower := by
  obtain ⟨q, ⟨E⟩⟩ := exists_exactStablePartnerEnumeration P m
  obtain ⟨j, hj⟩ := E.complete base hbase
  obtain ⟨W, S, hbound⟩ :=
    exists_exact_support_with_nearest_window_bound P E base revealed hbase hj
  exact ⟨q, E, j, hj, W, S, hbound⟩

end StableMatchings355
