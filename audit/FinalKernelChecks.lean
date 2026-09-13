import StableMatchingsE2E.FinalTheorem

open StableMatchingsE2E

-- Frozen signatures.  These `#check`s fail if a hidden hypothesis is added.
#check (stableCount_nat_bound_seventeen_fifths :
  ∀ (n : Nat), 1 ≤ n → ∀ P : ProfileCode n,
    5 ^ n * stableCount P < 17 ^ n)

#check (SM_nat_bound_seventeen_fifths :
  ∀ (n : Nat), 1 ≤ n → 5 ^ n * SM n < 17 ^ n)

#check (stableCount_lt_seventeen_fifths_pow :
  ∀ (n : Nat), 1 ≤ n → ∀ P : ProfileCode n,
    (stableCount P : Real) < ((17 : Real) / 5) ^ n)

#check (SM_lt_seventeen_fifths_pow :
  ∀ (n : Nat), 1 ≤ n →
    (SM n : Real) < ((17 : Real) / 5) ^ n)

-- End-to-end dependency spine and all four headline declarations.
#print axioms map_assemblePriority_splitTargetPriorityMeasure
#print axioms exists_staticWindowData
#print axioms ae_lexTargetMarkerLogNN_assemble_eq_actual
#print axioms lintegral_actualMarkerPair_le_geometric
#print axioms lintegral_unit_actualMarkerPair_lt_log_seventeen_div_five
#print axioms lintegral_full_lexTargetMarkerLogNN_lt
#print axioms log_stableCount_lt_n_log_seventeen_fifths
#print axioms stableCount_nat_bound_seventeen_fifths
#print axioms SM_nat_bound_seventeen_fifths
#print axioms stableCount_lt_seventeen_fifths_pow
#print axioms SM_lt_seventeen_fifths_pow
