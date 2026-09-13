import StableMatchingsE2E.ProfileCode

namespace StableMatchingsE2E

/-! Exact arithmetic adapter between the kernel-facing natural-number target
and the corresponding real exponential bound. -/

theorem nat_scaled_lt_iff_real_bound (a n : Nat) :
    5 ^ n * a < 17 ^ n ↔ (a : Real) < ((17 : Real) / 5) ^ n := by
  have hfive : 0 < (5 : Real) ^ n := pow_pos (by norm_num) n
  rw [div_pow, (lt_div_iff₀ hfive)]
  norm_cast
  exact Nat.mul_comm (5 ^ n) a ▸ Iff.rfl

theorem stableCount_lt_seventeen_fifths_pow_of_nat_bound
    (n : Nat) (P : ProfileCode n)
    (h : 5 ^ n * stableCount P < 17 ^ n) :
    (stableCount P : Real) < ((17 : Real) / 5) ^ n :=
  (nat_scaled_lt_iff_real_bound (stableCount P) n).mp h

theorem SM_lt_seventeen_fifths_pow_of_nat_bound
    (n : Nat) (h : 5 ^ n * SM n < 17 ^ n) :
    (SM n : Real) < ((17 : Real) / 5) ^ n :=
  (nat_scaled_lt_iff_real_bound (SM n) n).mp h

theorem SM_nat_bound_of_all_profiles (n : Nat)
    (h : ∀ P : ProfileCode n, 5 ^ n * stableCount P < 17 ^ n) :
    5 ^ n * SM n < 17 ^ n := by
  obtain ⟨P, hP⟩ := exists_profile_attaining_SM n
  simpa [hP] using h P

end StableMatchingsE2E
