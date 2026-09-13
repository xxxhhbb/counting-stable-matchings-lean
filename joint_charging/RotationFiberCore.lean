import «BoundaryDeletionCore»
import Mathlib.Tactic

namespace StableMatchingsJointCharging

/-!
The exact conditional-fiber implication used by the extra-left charge.

For each participant, the rotations involving it form an ordered chain.  A
stable matching selects an initial segment, encoded by `cut`; the participant's
stable partner is an injective function of that cut.  These are precisely the
two standard rotation-system facts needed below.  No probability or entropy
argument is hidden in this module.
-/

section RotationCut

variable {Ω R P W : Type*} [DecidableEq R]

variable
  (ideal : Ω → Finset R)
  (partner : Ω → P → W)
  (involves : P → R → Prop)
  (position : P → R → ℕ)
  (cut : Ω → P → ℕ)
  (partnerAt : P → ℕ → W)

/-- Exact partner equality identifies the participant-chain cut. -/
theorem cut_eq_of_partner_eq
    (hpartner : ∀ ω p, partner ω p = partnerAt p (cut ω p))
    (hinjective : ∀ p, Function.Injective (partnerAt p))
    {ω ν : Ω} {p : P}
    (heq : partner ν p = partner ω p) :
    cut ν p = cut ω p := by
  apply hinjective p
  rw [← hpartner ν p, ← hpartner ω p]
  exact heq

/-- Fixing one participant's exact stable partner preserves membership of
every rotation on that participant's chain. -/
theorem rotation_membership_iff_of_partner_eq
    (hpartner : ∀ ω p, partner ω p = partnerAt p (cut ω p))
    (hinjective : ∀ p, Function.Injective (partnerAt p))
    (hmem : ∀ ω p r, involves p r →
      (r ∈ ideal ω ↔ position p r < cut ω p))
    {ω ν : Ω} {p : P}
    (heq : partner ν p = partner ω p)
    {r : R} (hpr : involves p r) :
    r ∈ ideal ν ↔ r ∈ ideal ω := by
  have hcut : cut ν p = cut ω p :=
    cut_eq_of_partner_eq partner cut partnerAt hpartner hinjective heq
  rw [hmem ν p r hpr, hmem ω p r hpr, hcut]

/-- Direct witness form: if the base matching contains a rotation involving
`p`, then every matching in the exact one-coordinate partner fiber contains
that rotation as well. -/
theorem included_rotation_forced_in_partner_fiber
    (hpartner : ∀ ω p, partner ω p = partnerAt p (cut ω p))
    (hinjective : ∀ p, Function.Injective (partnerAt p))
    (hmem : ∀ ω p r, involves p r →
      (r ∈ ideal ω ↔ position p r < cut ω p))
    {ω ν : Ω} {p : P} {r : R}
    (hrω : r ∈ ideal ω) (hpr : involves p r)
    (heq : partner ν p = partner ω p) :
    r ∈ ideal ν := by
  exact (rotation_membership_iff_of_partner_eq
    ideal partner involves position cut partnerAt
    hpartner hinjective hmem heq hpr).2 hrω

end RotationCut

section AboveWitness

variable {Ω R P W : Type*} [PartialOrder R] [DecidableEq R]

/-- The nonmaximal case of the extra-left witness.  Exact partner equality
forces an included later rotation `s`; ideal closure then forces every
earlier rotation `r ≤ s`. -/
theorem earlier_rotation_forced_by_later_partner_witness
    (ideal : Ω → Finset R)
    (partner : Ω → P → W)
    (involves : P → R → Prop)
    (position : P → R → ℕ)
    (cut : Ω → P → ℕ)
    (partnerAt : P → ℕ → W)
    (hpartner : ∀ ω p, partner ω p = partnerAt p (cut ω p))
    (hinjective : ∀ p, Function.Injective (partnerAt p))
    (hmem : ∀ ω p r, involves p r →
      (r ∈ ideal ω ↔ position p r < cut ω p))
    (hideal : ∀ ω, IsFinsetIdeal (ideal ω))
    {ω ν : Ω} {p : P} {r s : R}
    (hrs : r ≤ s) (hsω : s ∈ ideal ω) (hps : involves p s)
    (heq : partner ν p = partner ω p) :
    r ∈ ideal ν := by
  have hsν : s ∈ ideal ν :=
    included_rotation_forced_in_partner_fiber
      ideal partner involves position cut partnerAt
      hpartner hinjective hmem hsω hps heq
  exact hideal ν hrs hsν

end AboveWitness

end StableMatchingsJointCharging
