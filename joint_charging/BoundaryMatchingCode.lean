import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace StableMatchingsJointCharging

/-!
The finite counting interface for the boundary graph.

After choosing the unmatched set `u`, a perfect matching of a disjoint union
of paths and even cycles is determined by one bit per cycle.  The graph-theory
layer must construct `encode` and prove its injectivity.  This module proves
the entire remaining cardinal arithmetic, including the `2^(n/4)` exponent.
-/

theorem card_le_two_pow_of_injective_cycle_code
    {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (encode : X → C → Bool) (hinj : Function.Injective encode) :
    Fintype.card X ≤ 2 ^ Fintype.card C := by
  have h := Fintype.card_le_of_injective encode hinj
  simpa using h

/-- Combined unmatched-set/cycle-bit code.  `U` is the type of admissible
unmatched sets and `C` is the type of cycle components. -/
theorem boundary_matching_code_bound
    {X U C : Type*} [Fintype X] [Fintype U] [Fintype C] [DecidableEq C]
    (n budget : ℕ)
    (encode : X → U × (C → Bool))
    (hinj : Function.Injective encode)
    (hU : Fintype.card U ≤ budget)
    (hcycles : 4 * Fintype.card C ≤ n) :
    Fintype.card X ≤ 2 ^ (n / 4) * budget := by
  have hcode := Fintype.card_le_of_injective encode hinj
  have hc : Fintype.card C ≤ n / 4 := by omega
  have hpow : 2 ^ Fintype.card C ≤ 2 ^ (n / 4) :=
    pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hc
  calc
    Fintype.card X ≤ Fintype.card U * 2 ^ Fintype.card C := by
      simpa using hcode
    _ ≤ budget * 2 ^ (n / 4) := Nat.mul_le_mul hU hpow
    _ = 2 ^ (n / 4) * budget := Nat.mul_comm _ _

/-- Exact interface used in the paper: once admissible unmatched sets are
bounded by a binomial prefix, the fixed-image deletion fiber obeys the stated
boundary budget. -/
theorem boundary_matching_binomial_prefix_bound
    {X U C : Type*} [Fintype X] [Fintype U] [Fintype C] [DecidableEq C]
    (n k : ℕ)
    (encode : X → U × (C → Bool))
    (hinj : Function.Injective encode)
    (hU : Fintype.card U ≤ ∑ i ∈ Finset.range (k + 1), n.choose i)
    (hcycles : 4 * Fintype.card C ≤ n) :
    Fintype.card X ≤
      2 ^ (n / 4) * ∑ i ∈ Finset.range (k + 1), n.choose i := by
  exact boundary_matching_code_bound n
    (∑ i ∈ Finset.range (k + 1), n.choose i)
    encode hinj hU hcycles

end StableMatchingsJointCharging
