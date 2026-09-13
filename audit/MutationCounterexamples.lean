import StableMatchingsE2E

namespace StableMatchingsE2E.Validation

open StableMatchingsE2E
open scoped unitInterval BigOperators

/-! Semantic mutation tests.  These are positive kernel proofs that the named
mutations are invalid; they do not modify the production source. -/

/-- Dropping `1 ≤ n` makes the strict target false at `n = 0`. -/
theorem removing_hn_is_false :
    ¬ (5 ^ (0 : Nat) * stableCount (identityProfile 0) < 17 ^ (0 : Nat)) := by
  rw [stableCount_zero]
  norm_num

/-- Reversing the strict target inequality already fails for the unit count at `n = 1`. -/
theorem reversing_strict_inequality_is_false :
    ¬ (17 ^ (1 : Nat) < 5 ^ (1 : Nat) * 1) := by
  norm_num

/-- Omitting the `+1` in the two-sided zero-based geometric window changes
the value even at the first-success pair `(0,0)`. -/
theorem deleting_geometric_offset_changes_window :
    geometricWindow (0, 0) ≠ (0 : Nat) + 0 := by
  norm_num [geometricWindow]

/-- Treating both zero-based geometric variables as one-based would add two
rather than the single overlap-corrected offset; that mutation is also false. -/
theorem double_geometric_offset_changes_window :
    geometricWindow (0, 0) ≠ (0 : Nat) + 0 + 2 := by
  norm_num [geometricWindow]

/-- The positive-parameter geometric mass formula cannot be applied at
`x = 0`: the totalized endpoint is a Dirac law and the window equals one. -/
theorem deleting_geometric_nonzero_guard_is_false :
    (GeometricPairMeasure (0 : I)).real
        {z : Nat × Nat | geometricWindow z = 1} ≠
      (1 : Real) * ((0 : Real) ^ 2 * (1 - 0) ^ ((1 : Nat) - 1)) := by
  rw [geometricWindow_zero_fiber]
  norm_num

/-- A non-strict analytic bound alone cannot yield a strict bound without a
separate gap argument. -/
theorem nonstrict_does_not_imply_strict :
    ¬ (∀ a b : Real, a ≤ b → a < b) := by
  intro h
  exact (lt_irrefl (0 : Real)) (h 0 0 le_rfl)

/-- Marginal laws do not determine the joint law: two identical fair bits
have the same fair marginal but never realize `(true,false)`. -/
def fairMass (b : Bool) : Rat := 1 / 2

def diagonalJointMass (p : Bool × Bool) : Rat :=
  if p.1 = p.2 then 1 / 2 else 0

theorem diagonal_has_fair_first_marginal (b : Bool) :
    (∑ c : Bool, diagonalJointMass (b, c)) = fairMass b := by
  cases b <;> norm_num [diagonalJointMass, fairMass]

theorem diagonal_has_fair_second_marginal (b : Bool) :
    (∑ c : Bool, diagonalJointMass (c, b)) = fairMass b := by
  cases b <;> norm_num [diagonalJointMass, fairMass]

theorem diagonal_is_not_product :
    diagonalJointMass (true, false) ≠ fairMass true * fairMass false := by
  norm_num [diagonalJointMass, fairMass]

/-- Even from two fair source bits, choosing a coordinate after observing a
bit can bias the selected bit.  This is the finite analogue of why the stable
partner enumeration must be fixed before the reveal prefix. -/
def adaptiveSelectedBit (p : Bool × Bool) : Bool :=
  if p.1 then p.1 else p.2

def fairPairMass (_p : Bool × Bool) : Rat := 1 / 4

theorem adaptive_coordinate_selection_is_biased :
    (∑ p : Bool × Bool,
        if adaptiveSelectedBit p then fairPairMass p else 0) = 3 / 4 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  norm_num [adaptiveSelectedBit, fairPairMass]

theorem adaptive_coordinate_selection_not_fair :
    (∑ p : Bool × Bool,
        if adaptiveSelectedBit p then fairPairMass p else 0) ≠ 1 / 2 := by
  rw [adaptive_coordinate_selection_is_biased]
  norm_num

/-- A non-involutive permutation witnesses why a woman's partner is
`mu.symm w`, not `mu w`. -/
def threeCycle : Equiv.Perm (Fin 3) :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

theorem forward_and_inverse_partner_can_differ :
    threeCycle (0 : Fin 3) ≠ threeCycle.symm (0 : Fin 3) := by
  decide

/-- A strict order on raw priorities cannot itself order tied coordinates;
the production `priorityOrder` therefore needs its deterministic index
tie-break. -/
theorem raw_priority_strict_order_cannot_rank_constant_pair :
    ¬ ∃ order : Equiv.Perm (Fin 2),
      ∀ p q : Fin 2,
        (order.symm p).val < (order.symm q).val ↔
          ((0 : Nat) < 0) := by
  rintro ⟨order, h⟩
  let p := order 0
  let q := order 1
  have hpq := h p q
  have : (0 : Nat) < 1 := by norm_num
  have hpos : (order.symm p).val < (order.symm q).val := by
    simpa [p, q] using this
  exact (by simpa using hpq.mp hpos)

end StableMatchingsE2E.Validation

#print axioms StableMatchingsE2E.Validation.removing_hn_is_false
#print axioms StableMatchingsE2E.Validation.deleting_geometric_nonzero_guard_is_false
#print axioms StableMatchingsE2E.Validation.diagonal_is_not_product
#print axioms StableMatchingsE2E.Validation.adaptive_coordinate_selection_is_biased
#print axioms StableMatchingsE2E.Validation.forward_and_inverse_partner_can_differ
#print axioms StableMatchingsE2E.Validation.raw_priority_strict_order_cannot_rank_constant_pair
