import StableMatchingsE2E.ProfileCode

/-!
# Replication of stable-marriage profiles

This file constructs a block product of identical strict complete profiles.
Every participant ranks all partners in its own block before every partner outside
that block.  Independent stable matchings in the blocks therefore give a
stable matching of the product profile.
-/

namespace StableMatchingsE2E

open Equiv

private def blockIndexPerm {t : Nat} [NeZero t] (i : Fin t) : Equiv.Perm (Fin t) :=
  Equiv.swap 0 i

private def blockRankPerm {n t : Nat} [NeZero t]
    (i : Fin t) (sigma : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (t * n)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (blockIndexPerm i) sigma).trans finProdFinEquiv)

/-- The `t`-fold block product of `P`.  Inside its own block a participant uses
the preferences of `P`; every own-block partner precedes every outside-block
partner. -/
def replicatedProfile {n t : Nat} [NeZero t] (P : ProfileCode n) :
    ProfileCode (t * n) where
  manRank x :=
    let xm := finProdFinEquiv.symm x
    blockRankPerm xm.1 (P.manRank xm.2)
  womanRank x :=
    let xw := finProdFinEquiv.symm x
    blockRankPerm xw.1 (P.womanRank xw.2)

private def productMatchingEquiv {n t : Nat}
    (mu : Fin t → MatchingCode n) : Equiv.Perm (Fin t × Fin n) where
  toFun x := (x.1, mu x.1 x.2)
  invFun x := (x.1, (mu x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Combine one perfect matching from each block into a perfect matching of
the replicated profile. -/
def replicatedMatching {n t : Nat} (mu : Fin t → MatchingCode n) :
    MatchingCode (t * n) :=
  finProdFinEquiv.symm.trans ((productMatchingEquiv mu).trans finProdFinEquiv)

@[simp] theorem replicatedMatching_apply {n t : Nat}
    (mu : Fin t → MatchingCode n) (i : Fin t) (m : Fin n) :
    replicatedMatching mu (finProdFinEquiv (i, m)) =
      finProdFinEquiv (i, mu i m) := by
  simp [replicatedMatching, productMatchingEquiv]

@[simp] theorem replicatedMatching_symm_apply {n t : Nat}
    (mu : Fin t → MatchingCode n) (i : Fin t) (w : Fin n) :
    (replicatedMatching mu).symm (finProdFinEquiv (i, w)) =
      finProdFinEquiv (i, (mu i).symm w) := by
  simp [replicatedMatching, productMatchingEquiv]

private theorem finProdFinEquiv_val {n t : Nat} (i : Fin t) (x : Fin n) :
    (finProdFinEquiv (i, x)).val = x.val + n * i.val := by
  simp [finProdFinEquiv]

private theorem own_block_rank_lt_outside_rank {n t : Nat}
    [NeZero t] (i j : Fin t) (hji : j ≠ i)
    (sigma : Equiv.Perm (Fin n)) (x y : Fin n) :
    (blockRankPerm i sigma (finProdFinEquiv (i, x))).val <
      (blockRankPerm i sigma (finProdFinEquiv (j, y))).val := by
  rw [show blockRankPerm i sigma (finProdFinEquiv (i, x)) =
      finProdFinEquiv (0, sigma x) by
        simp [blockRankPerm, blockIndexPerm]]
  rw [show blockRankPerm i sigma (finProdFinEquiv (j, y)) =
      finProdFinEquiv (blockIndexPerm i j, sigma y) by
        simp [blockRankPerm]]
  rw [finProdFinEquiv_val, finProdFinEquiv_val]
  have hswap : blockIndexPerm i j ≠ 0 := by
    intro h
    apply hji
    calc
      j = blockIndexPerm i (blockIndexPerm i j) := by
        simp [blockIndexPerm]
      _ = blockIndexPerm i 0 := congrArg (blockIndexPerm i) h
      _ = i := by simp [blockIndexPerm]
  have hpos : 0 < (blockIndexPerm i j).val :=
    Nat.pos_of_ne_zero (by
      intro hz
      apply hswap
      apply Fin.ext
      simpa using hz)
  have hx : (sigma x).val < n := (sigma x).isLt
  have hmult : n * 1 ≤ n * (blockIndexPerm i j).val :=
    Nat.mul_le_mul_left n hpos
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero]
  omega

private theorem replicatedProfile_man_rank_apply {n t : Nat} [NeZero t]
    (P : ProfileCode n) (i : Fin t) (m : Fin n) (j : Fin t) (w : Fin n) :
    (replicatedProfile (t := t) P).manRank (finProdFinEquiv (i, m))
        (finProdFinEquiv (j, w)) =
      blockRankPerm i (P.manRank m) (finProdFinEquiv (j, w)) := by
  have hdecode := finProdFinEquiv.symm_apply_apply (i, m)
  simp only [replicatedProfile]
  rw [hdecode]

private theorem replicatedProfile_woman_rank_apply {n t : Nat} [NeZero t]
    (P : ProfileCode n) (i : Fin t) (w : Fin n) (j : Fin t) (m : Fin n) :
    (replicatedProfile (t := t) P).womanRank (finProdFinEquiv (i, w))
        (finProdFinEquiv (j, m)) =
      blockRankPerm i (P.womanRank w) (finProdFinEquiv (j, m)) := by
  have hdecode := finProdFinEquiv.symm_apply_apply (i, w)
  simp only [replicatedProfile]
  rw [hdecode]

private theorem same_block_man_rank {n t : Nat} [NeZero t]
    (P : ProfileCode n) (i : Fin t) (m x : Fin n) :
    (replicatedProfile (t := t) P).manRank (finProdFinEquiv (i, m))
        (finProdFinEquiv (i, x)) =
      finProdFinEquiv (0, P.manRank m x) := by
  rw [replicatedProfile_man_rank_apply]
  simp [blockRankPerm, blockIndexPerm]

private theorem same_block_woman_rank {n t : Nat} [NeZero t]
    (P : ProfileCode n) (i : Fin t) (w x : Fin n) :
    (replicatedProfile (t := t) P).womanRank (finProdFinEquiv (i, w))
        (finProdFinEquiv (i, x)) =
      finProdFinEquiv (0, P.womanRank w x) := by
  rw [replicatedProfile_woman_rank_apply]
  simp [blockRankPerm, blockIndexPerm]

theorem replicatedMatching_stable {n t : Nat} [NeZero t]
    (P : ProfileCode n) (mu : Fin t → MatchingCode n)
    (hmu : ∀ i, Stable P (mu i)) :
    Stable (replicatedProfile (t := t) P) (replicatedMatching mu) := by
  intro man woman hblocks
  obtain ⟨⟨i, m⟩, rfl⟩ := finProdFinEquiv.surjective man
  obtain ⟨⟨j, w⟩, rfl⟩ := finProdFinEquiv.surjective woman
  by_cases hsame : j = i
  · subst j
    apply hmu i m w
    constructor
    · have h := hblocks.1
      rw [replicatedMatching_apply, same_block_man_rank,
        same_block_man_rank] at h
      change (finProdFinEquiv (0, P.manRank m w)).val <
        (finProdFinEquiv (0, P.manRank m (mu i m))).val at h
      rw [finProdFinEquiv_val, finProdFinEquiv_val] at h
      simpa using h
    · have h := hblocks.2
      rw [replicatedMatching_symm_apply, same_block_woman_rank,
        same_block_woman_rank] at h
      change (finProdFinEquiv (0, P.womanRank w m)).val <
        (finProdFinEquiv (0, P.womanRank w ((mu i).symm w))).val at h
      rw [finProdFinEquiv_val, finProdFinEquiv_val] at h
      simpa using h
  · have hown := own_block_rank_lt_outside_rank i j hsame
      (P.manRank m) (mu i m) w
    have hnot : ¬
        (replicatedProfile (t := t) P).manRank (finProdFinEquiv (i, m))
            (finProdFinEquiv (j, w)) <
          (replicatedProfile (t := t) P).manRank (finProdFinEquiv (i, m))
            (replicatedMatching mu (finProdFinEquiv (i, m))) := by
      rw [replicatedMatching_apply]
      rw [replicatedProfile_man_rank_apply,
        replicatedProfile_man_rank_apply]
      exact (Nat.not_lt_of_ge hown.le)
    exact hnot hblocks.1

theorem replicatedMatching_injective {n t : Nat} :
    Function.Injective (replicatedMatching :
      (Fin t → MatchingCode n) → MatchingCode (t * n)) := by
  intro mu nu h
  funext i
  apply Equiv.ext
  intro m
  have happ := congrArg (fun e : MatchingCode (t * n) =>
    e (finProdFinEquiv (i, m))) h
  simp only [replicatedMatching_apply] at happ
  exact congrArg Prod.snd (finProdFinEquiv.injective happ)

/-- Independent stable choices in the `t` blocks inject into stable
matchings of the replicated profile. -/
def replicationEmbedding {n t : Nat} [NeZero t] (P : ProfileCode n) :
    (Fin t → ↥(stableSet P)) ↪ ↥(stableSet (replicatedProfile (t := t) P)) where
  toFun choices := ⟨replicatedMatching (fun i => (choices i).1), by
    apply (mem_stableSet_iff _ _).2
    apply replicatedMatching_stable P
    intro i
    exact (mem_stableSet_iff P (choices i).1).1 (choices i).2⟩
  inj' := by
    intro a b hab
    have hmatching : replicatedMatching (fun i => (a i).1) =
        replicatedMatching (fun i => (b i).1) :=
      congrArg Subtype.val hab
    have hfunctions : (fun i => (a i).1) = (fun i => (b i).1) :=
      replicatedMatching_injective hmatching
    funext i
    apply Subtype.ext
    exact congrFun hfunctions i

theorem stableCount_pow_le_replicated {n t : Nat} [NeZero t]
    (P : ProfileCode n) :
    stableCount P ^ t ≤ stableCount (replicatedProfile (t := t) P) := by
  have hcard : Fintype.card (Fin t → ↥(stableSet P)) ≤
      Fintype.card ↥(stableSet (replicatedProfile (t := t) P)) :=
    Fintype.card_le_of_injective
      (replicationEmbedding P) (replicationEmbedding P).injective
  simpa [stableCount] using hcard

/-- The extremal stable-matching count is supermultiplicative under
replication. -/
theorem SM_pow_le_SM_mul (n t : Nat) [NeZero t] :
    SM n ^ t ≤ SM (t * n) := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  calc
    SM n ^ t = stableCount P ^ t := by rw [hP]
    _ ≤ stableCount (replicatedProfile (t := t) P) :=
      stableCount_pow_le_replicated P
    _ ≤ SM (t * n) := SM_spec _

end StableMatchingsE2E
