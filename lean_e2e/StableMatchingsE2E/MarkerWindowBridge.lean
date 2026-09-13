import StableMatchingsE2E.MarkerOwners
import StableMatchingsEntropy.Core

namespace StableMatchingsE2E

open StableMatchings355
open StableMatchingsEntropy

/-! This module identifies the actual nearest-revealed-owner window with the
finite two-sided Boolean marker window used by the entropy argument. -/

def ownerMarkerBit {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (h : Fin q) : Bool :=
  decide (revealed (stablePartnerOwner E base h))

@[simp] theorem ownerMarkerBit_eq_true_iff {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (h : Fin q) :
    ownerMarkerBit E base revealed h = true ↔
      revealed (stablePartnerOwner E base h) := by
  simp [ownerMarkerBit]

def leftMarkerIndex {q : Nat} (j : Fin q) (i : Fin j.val) : Fin q :=
  ⟨j.val - 1 - i.val, by omega⟩

def rightMarkerIndex {q : Nat} (j : Fin q)
    (i : Fin (q - (j.val + 1))) : Fin q :=
  ⟨j.val + 1 + i.val, by omega⟩

/-- Marker bits scanned from `j-1,j-2,…,0`. -/
def leftMarkerBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q) : List Bool :=
  List.ofFn fun i : Fin j.val =>
    ownerMarkerBit E base revealed (leftMarkerIndex j i)

/-- Marker bits scanned from `j+1,j+2,…,q-1`. -/
def rightMarkerBits {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q) : List Bool :=
  List.ofFn fun i : Fin (q - (j.val + 1)) =>
    ownerMarkerBit E base revealed (rightMarkerIndex j i)

@[simp] theorem leftMarkerBits_length {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q) :
    (leftMarkerBits E base revealed j).length = j.val := by
  simp [leftMarkerBits]

@[simp] theorem rightMarkerBits_length {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q) :
    (rightMarkerBits E base revealed j).length = q - (j.val + 1) := by
  simp [rightMarkerBits]

@[simp] theorem leftMarkerBits_get {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q) (i : Fin j.val) :
    (leftMarkerBits E base revealed j).get
        ⟨i.val, by simp⟩ =
      ownerMarkerBit E base revealed (leftMarkerIndex j i) := by
  simp [leftMarkerBits]

@[simp] theorem rightMarkerBits_get {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q)
    (i : Fin (q - (j.val + 1))) :
    (rightMarkerBits E base revealed j).get
        ⟨i.val, by simp⟩ =
      ownerMarkerBit E base revealed (rightMarkerIndex j i) := by
  simp [rightMarkerBits]

private theorem truncatedWait_eq_succ_of_first_true
    (xs : List Bool) (r : Nat) (hr : r < xs.length)
    (hbefore : ∀ i, i < r → ∀ hi : i < xs.length, xs[i] = false)
    (hat : xs[r] = true) :
    truncatedWait xs = r + 1 := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons b xs ih =>
      cases r with
      | zero =>
          have hb : b = true := by simpa using hat
          simp [hb]
      | succ r =>
          have hb : b = false := by
            have hb' := hbefore 0 (by omega) (by simp)
            change b = false at hb'
            exact hb'
          have hr' : r < xs.length := by simpa using hr
          have hbefore' : ∀ i, i < r → ∀ hi : i < xs.length, xs[i] = false := by
            intro i hir hi
            have hi' := hbefore (i + 1) (by omega) (by simp; omega)
            change xs[i] = false at hi'
            exact hi'
          have hat' : xs[r] = true := by
            change xs[r] = true at hat
            exact hat
          simp only [hb, truncatedWait]
          rw [ih r hr' hbefore' hat']
          omega

private theorem marker_at_index_of_bit_true {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] {h : Fin q}
    (hb : ownerMarkerBit E base revealed h = true) :
    IsRevealedMarker E base revealed h (stablePartnerOwner E base h) := by
  exact (marker_at_owner_iff E base revealed h).2
    ((ownerMarkerBit_eq_true_iff E base revealed h).1 hb)

theorem left_truncatedWait_eq_boundary {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q)
    (W : NearestRevealedWindow E base revealed j) :
    truncatedWait (leftMarkerBits E base revealed j) =
      j.val - lowerBoundary W.lower + 1 := by
  classical
  cases hW : W.lower with
  | none =>
      have hno : true ∉ leftMarkerBits E base revealed j := by
        intro hm
        rw [List.mem_iff_getElem] at hm
        obtain ⟨i, hi, hbit⟩ := hm
        have hb : ownerMarkerBit E base revealed
            (leftMarkerIndex j ⟨i, by simpa using hi⟩) = true := by
          simpa [leftMarkerBits] using hbit
        have hmarker := marker_at_index_of_bit_true E base revealed hb
        have hlt : (leftMarkerIndex j ⟨i, by simpa using hi⟩).val < j.val := by
          have hi' : i < j.val := by simpa using hi
          simp [leftMarkerIndex]
          omega
        exact W.lower_none hW _ _ hmarker hlt
      rw [truncatedWait_eq_length_succ_of_no_marker _ hno]
      simp [lowerBoundary]
  | some hp =>
      rcases hp with ⟨h, p⟩
      obtain ⟨hm, hhj⟩ := W.lower_valid h p hW
      let r := j.val - h.val - 1
      have hr : r < (leftMarkerBits E base revealed j).length := by
        simp [r]
        omega
      have hindex : leftMarkerIndex j ⟨r, by simpa using hr⟩ = h := by
        apply Fin.eq_of_val_eq
        simp [leftMarkerIndex, r]
        omega
      have hat : (leftMarkerBits E base revealed j)[r] = true := by
        have hrev : revealed (stablePartnerOwner E base h) := by
          have hpowner : p = stablePartnerOwner E base h :=
            marker_owner_unique E base revealed hm
          simpa [← hpowner] using hm.1
        simp [leftMarkerBits, hindex, hrev]
      have hbefore : ∀ i, i < r →
          ∀ hi : i < (leftMarkerBits E base revealed j).length,
            (leftMarkerBits E base revealed j)[i] = false := by
        intro i hir hi
        by_contra hfalse
        have htrue : (leftMarkerBits E base revealed j)[i] = true := by
          cases hv : (leftMarkerBits E base revealed j)[i] <;> simp_all
        have hb : ownerMarkerBit E base revealed
            (leftMarkerIndex j ⟨i, by simpa using hi⟩) = true := by
          simpa [leftMarkerBits] using htrue
        have hmarker := marker_at_index_of_bit_true E base revealed hb
        have hidxltj : (leftMarkerIndex j ⟨i, by simpa using hi⟩).val < j.val := by
          have hi' : i < j.val := by simpa using hi
          simp [leftMarkerIndex]
          omega
        have hmax := W.lower_maximal h p hW _ _ hmarker hidxltj
        have hidxgt : h.val < (leftMarkerIndex j ⟨i, by simpa using hi⟩).val := by
          simp [leftMarkerIndex, r] at hir ⊢
          omega
        omega
      rw [truncatedWait_eq_succ_of_first_true _ r hr hbefore hat]
      simp [lowerBoundary, r]
      omega

theorem right_truncatedWait_eq_boundary {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q)
    (W : NearestRevealedWindow E base revealed j) :
    truncatedWait (rightMarkerBits E base revealed j) =
      upperBoundary W.upper - j.val := by
  classical
  cases hW : W.upper with
  | none =>
      have hno : true ∉ rightMarkerBits E base revealed j := by
        intro hm
        rw [List.mem_iff_getElem] at hm
        obtain ⟨i, hi, hbit⟩ := hm
        have hb : ownerMarkerBit E base revealed
            (rightMarkerIndex j ⟨i, by simpa using hi⟩) = true := by
          simpa [rightMarkerBits] using hbit
        have hmarker := marker_at_index_of_bit_true E base revealed hb
        have hlt : j.val < (rightMarkerIndex j ⟨i, by simpa using hi⟩).val := by
          simp [rightMarkerIndex]
          omega
        exact W.upper_none hW _ _ hmarker hlt
      rw [truncatedWait_eq_length_succ_of_no_marker _ hno]
      simp [upperBoundary]
      omega
  | some hp =>
      rcases hp with ⟨h, p⟩
      obtain ⟨hm, hjh⟩ := W.upper_valid h p hW
      let r := h.val - j.val - 1
      have hr : r < (rightMarkerBits E base revealed j).length := by
        simp [r]
        omega
      have hindex : rightMarkerIndex j ⟨r, by simpa using hr⟩ = h := by
        apply Fin.eq_of_val_eq
        simp [rightMarkerIndex, r]
        omega
      have hat : (rightMarkerBits E base revealed j)[r] = true := by
        have hrev : revealed (stablePartnerOwner E base h) := by
          have hpowner : p = stablePartnerOwner E base h :=
            marker_owner_unique E base revealed hm
          simpa [← hpowner] using hm.1
        simp [rightMarkerBits, hindex, hrev]
      have hbefore : ∀ i, i < r →
          ∀ hi : i < (rightMarkerBits E base revealed j).length,
            (rightMarkerBits E base revealed j)[i] = false := by
        intro i hir hi
        by_contra hfalse
        have htrue : (rightMarkerBits E base revealed j)[i] = true := by
          cases hv : (rightMarkerBits E base revealed j)[i] <;> simp_all
        have hb : ownerMarkerBit E base revealed
            (rightMarkerIndex j ⟨i, by simpa using hi⟩) = true := by
          simpa [rightMarkerBits] using htrue
        have hmarker := marker_at_index_of_bit_true E base revealed hb
        have hjidx : j.val < (rightMarkerIndex j ⟨i, by simpa using hi⟩).val := by
          simp [rightMarkerIndex]
          omega
        have hmin := W.upper_minimal h p hW _ _ hmarker hjidx
        have hidxlt : (rightMarkerIndex j ⟨i, by simpa using hi⟩).val < h.val := by
          simp [rightMarkerIndex, r] at hir ⊢
          omega
        omega
      rw [truncatedWait_eq_succ_of_first_true _ r hr hbefore hat]
      simp [upperBoundary, r]
      omega

theorem nearest_window_width_eq_markerWindowWidth {n q : Nat}
    {P : Profile (Fin n) (Fin n)} {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] (j : Fin q)
    (W : NearestRevealedWindow E base revealed j) :
    upperBoundary W.upper - lowerBoundary W.lower =
      markerWindowWidth (leftMarkerBits E base revealed j)
        (rightMarkerBits E base revealed j) := by
  rw [markerWindowWidth, left_truncatedWait_eq_boundary E base revealed j W,
    right_truncatedWait_eq_boundary E base revealed j W]
  have hw := actual_index_in_nearest_window W
  omega

theorem exact_conditional_support_length_le_markerWindowWidth {n q : Nat}
    (P : Profile (Fin n) (Fin n)) {target : Fin n}
    (E : ExactStablePartnerEnumeration (q := q) P target)
    (base : Matching (Fin n) (Fin n)) (revealed : Fin n → Prop)
    [DecidablePred revealed] {j : Fin q} (hbase : Stable P base)
    (hbaseTarget : base.manPartner target = E.ranked.partner j)
    (W : NearestRevealedWindow E base revealed j)
    (S : ExactConditionalIndexSupport P E base revealed) :
    S.indices.length ≤
      markerWindowWidth (leftMarkerBits E base revealed j)
        (rightMarkerBits E base revealed j) := by
  rw [← nearest_window_width_eq_markerWindowWidth E base revealed j W]
  exact exact_conditional_support_length_le P E base revealed hbase hbaseTarget W S

end StableMatchingsE2E
