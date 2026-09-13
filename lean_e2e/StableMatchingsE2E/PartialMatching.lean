import Mathlib

namespace StableMatchingsE2E

/-- None denotes being unmatched; every acceptable partner beats None. -/
def improves {A : Type} (rank : A → Nat) (candidate : A) : Option A → Prop
  | none => True
  | some incumbent => rank candidate < rank incumbent

structure IncompleteProfile (A B : Type) where
  acceptable : A → B → Prop
  manRank : A → B → Nat
  womanRank : B → A → Nat
  man_strict : ∀ a, Function.Injective (manRank a)
  woman_strict : ∀ b, Function.Injective (womanRank b)

structure PartialMatching (A B : Type) where
  left : A → Option B
  right : B → Option A
  reciprocal : ∀ a b, left a = some b ↔ right b = some a

namespace PartialMatching
variable {A B : Type}

@[ext] theorem ext {M N : PartialMatching A B}
    (hl : M.left = N.left) (hr : M.right = N.right) : M=N := by
  cases M; cases N; cases hl; cases hr; rfl

instance [Finite A] [Finite B] : Finite (PartialMatching A B) :=
  Finite.of_injective (fun M : PartialMatching A B ↦ (M.left,M.right))
    (fun _ _ h ↦ ext (congrArg Prod.fst h) (congrArg Prod.snd h))

def Stable (P : IncompleteProfile A B) (M : PartialMatching A B) : Prop :=
  (∀ a b, M.left a = some b → P.acceptable a b) ∧
  ∀ a b, P.acceptable a b →
    ¬ (improves (P.manRank a) b (M.left a) ∧
       improves (P.womanRank b) a (M.right b))

def matchedLeft (M : PartialMatching A B) : Set A := {a | ∃ b, M.left a = some b}
def matchedRight (M : PartialMatching A B) : Set B := {b | ∃ a, M.right b = some a}

theorem left_some_injective (M : PartialMatching A B) {a a' : A} {b : B}
    (ha : M.left a = some b) (ha' : M.left a' = some b) : a=a' := by
  exact Option.some.inj (((M.reciprocal a b).mp ha).symm.trans
    ((M.reciprocal a' b).mp ha'))

end PartialMatching

structure RoommatesProfile (V : Type) where
  acceptable : V → V → Prop
  symmetric : ∀ u v, acceptable u v ↔ acceptable v u
  irreflexive : ∀ u, ¬ acceptable u u
  rank : V → V → Nat
  strict : ∀ u, Function.Injective (rank u)

structure RoommatesMatching (V : Type) where
  partner : V → Option V
  reciprocal : ∀ u v, partner u = some v ↔ partner v = some u
  no_self : ∀ u, partner u ≠ some u

namespace RoommatesMatching
variable {V : Type}

@[ext] theorem ext {M N : RoommatesMatching V} (h : M.partner = N.partner) : M=N := by
  cases M; cases N; cases h; rfl

instance [Finite V] : Finite (RoommatesMatching V) :=
  Finite.of_injective (fun M : RoommatesMatching V ↦ M.partner) (fun _ _ h ↦ ext h)

def Stable (P : RoommatesProfile V) (M : RoommatesMatching V) : Prop :=
  (∀ u v, M.partner u = some v → P.acceptable u v) ∧
  ∀ u v, P.acceptable u v →
    ¬ (improves (P.rank u) v (M.partner u) ∧
       improves (P.rank v) u (M.partner v))

/-- The two occurrences of V are distinct bipartite sides. -/
def double (M : RoommatesMatching V) : PartialMatching V V where
  left := M.partner
  right := M.partner
  reciprocal := M.reciprocal

theorem double_injective : Function.Injective (double (V := V)) := by
  intro M N h
  exact ext (congrArg PartialMatching.left h)

end RoommatesMatching

def RoommatesProfile.double {V : Type} (P : RoommatesProfile V) : IncompleteProfile V V where
  acceptable := P.acceptable
  manRank := P.rank
  womanRank := P.rank
  man_strict := P.strict
  woman_strict := P.strict

theorem roommates_double_stable_iff {V : Type} (P : RoommatesProfile V)
    (M : RoommatesMatching V) : M.double.Stable P.double ↔ M.Stable P := Iff.rfl

def roommates_stable_double_embedding {V : Type} (P : RoommatesProfile V) :
    {M : RoommatesMatching V // M.Stable P} ↪
    {M : PartialMatching V V // M.Stable P.double} where
  toFun M := ⟨M.val.double, (roommates_double_stable_iff P M.val).mpr M.property⟩
  inj' := by
    intro M N h
    apply Subtype.ext
    apply RoommatesMatching.double_injective
    exact congrArg (fun z : {M : PartialMatching V V // M.Stable P.double} ↦ z.val) h

theorem roommates_stable_count_le_double {V : Type} [Finite V] (P : RoommatesProfile V) :
    Nat.card {M : RoommatesMatching V // M.Stable P} ≤
      Nat.card {M : PartialMatching V V // M.Stable P.double} :=
  Nat.card_le_card_of_injective _ (roommates_stable_double_embedding P).injective

end StableMatchingsE2E
