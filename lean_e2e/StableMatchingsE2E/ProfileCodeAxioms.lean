import StableMatchingsE2E.ProfileCode

#print axioms StableMatchingsE2E.blocks_iff_core
#print axioms StableMatchingsE2E.stableCode_iff_core
#print axioms StableMatchingsE2E.ProfileCode.ofCore_manPref_iff
#print axioms StableMatchingsE2E.ProfileCode.ofCore_womanPref_iff
#print axioms StableMatchingsE2E.stable_ofCore_iff
#print axioms StableMatchingsE2E.stable_full_ofCore_iff
#print axioms StableMatchingsE2E.every_core_profile_has_complete_code
#print axioms StableMatchingsE2E.mem_stableSet_iff
#print axioms StableMatchingsE2E.SM_spec
#print axioms StableMatchingsE2E.exists_profile_attaining_SM
#print axioms StableMatchingsE2E.SM_zero

-- Symbolic boundary/mutation checks for the empty market.
example : StableMatchingsE2E.SM 0 = 1 := StableMatchingsE2E.SM_zero
example : StableMatchingsE2E.SM 0 ≠ 0 := by
  rw [StableMatchingsE2E.SM_zero]
  decide
