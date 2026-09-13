import «BoundaryDeletionCore»
import «ImprovedConstant»
import Mathlib.Tactic

namespace StableMatchingsJointCharging

noncomputable section

/-- Convert the integer half-mass inequality into a normalized real average.
`total` is the sum of the integer charges. -/
theorem normalized_average_ge_half_threshold
    (M bad r total : ℕ) (hM : 0 < M)
    (hbad : 2 * bad ≤ M)
    (hcharge : (M - bad) * r ≤ total) :
    (r : ℝ) / 2 ≤ (M : ℝ)⁻¹ * (total : ℝ) := by
  have htotal : M * r ≤ 2 * total :=
    total_charge_half_lower M bad r total hbad hcharge
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcast : (M : ℝ) * (r : ℝ) ≤ 2 * (total : ℝ) := by
    exact_mod_cast htotal
  rw [inv_mul_eq_div]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hMreal).2
  nlinarith

/-- The integer threshold immediately above `3n/80` is strictly larger than
the corresponding real density. -/
theorem three_n_div_eighty_lt_floor_succ (n : ℕ) :
    (3 : ℝ) * (n : ℝ) / 80 < (((3 * n) / 80 + 1 : ℕ) : ℝ) := by
  have hrem : 3 * n < 80 * ((3 * n) / 80 + 1) := by
    omega
  have hcast : (3 * n : ℝ) < (80 * ((3 * n) / 80 + 1) : ℕ) := by
    exact_mod_cast hrem
  push_cast at hcast
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 80)]
  push_cast
  nlinarith

/-- Half of the objects carrying integer charge at least the first threshold
above `3n/80` forces normalized average charge strictly above `3n/160`. -/
theorem normalized_average_gt_three_n_over_160
    (n M bad total : ℕ) (hM : 0 < M)
    (hbad : 2 * bad ≤ M)
    (hcharge :
      (M - bad) * ((3 * n) / 80 + 1) ≤ total) :
    (3 : ℝ) * (n : ℝ) / 160 < (M : ℝ)⁻¹ * (total : ℝ) := by
  have havg := normalized_average_ge_half_threshold
    M bad ((3 * n) / 80 + 1) total hM hbad hcharge
  have hfloor := three_n_div_eighty_lt_floor_succ n
  nlinarith

/-- Final real charging multiplication.  A local payment of
`log(3/2)/30` per average unit of `k`, combined with average
`k > 3n/160`, yields the optimized joint slack. -/
theorem joint_charge_ge_optimized_delta
    (n : ℕ) (averageK jointCharge : ℝ)
    (haverage : (3 : ℝ) * (n : ℝ) / 160 ≤ averageK)
    (hlocal : Real.log ((3 : ℝ) / 2) / 30 * averageK ≤ jointCharge) :
    (n : ℝ) * optimizedJointDelta ≤ jointCharge := by
  have hlog : 0 ≤ Real.log ((3 : ℝ) / 2) := (log_three_halves_pos).le
  unfold optimizedJointDelta
  calc
    (n : ℝ) * (Real.log ((3 : ℝ) / 2) / 1600) =
        Real.log ((3 : ℝ) / 2) / 30 * ((3 : ℝ) * (n : ℝ) / 160) := by
      ring
    _ ≤ Real.log ((3 : ℝ) / 2) / 30 * averageK := by
      gcongr
    _ ≤ jointCharge := hlocal

end

end StableMatchingsJointCharging
