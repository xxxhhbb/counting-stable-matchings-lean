import StableMatchingsE2E.OptimizedFinalTheorem
import StableMatchingsE2E.Replication
import StableMatchingsE2E.FixedEdges
import «CanonicalUniformPaymentGlobal»

open StableMatchingsE2E
open StableMatchingsJointCharging

/-!
Unified axiom audit for the participant-count proof chain.

The first group checks the one-sided geometric baseline.  The second group
checks the replication bridge, rotation-boundary slack theorem, and direct
large-n 3.3248 endpoint.  The final all-size composition is checked in
`AllSizeRefinedEndpoint.lean`.
-/

#check StableMatchingsE2E.SM_nat_bound_1665987_div_500000
#print axioms StableMatchingsE2E.SM_nat_bound_1665987_div_500000
#print axioms StableMatchingsE2E.SM_lt_1665987_div_500000_pow
#check StableMatchingsE2E.SM_pow_le_SM_mul
#print axioms StableMatchingsE2E.SM_pow_le_SM_mul
#check StableMatchingsE2E.fixedFiber_card_le_SM
#print axioms StableMatchingsE2E.fixedFiber_card_le_SM
#check StableMatchingsE2E.prescribedFiber_card_le_SM
#print axioms StableMatchingsE2E.prescribedFiber_card_le_SM

#check StableMatchingsJointCharging.all_profiles_nearCriticalUniformJointSlack
#print axioms StableMatchingsJointCharging.all_profiles_nearCriticalUniformJointSlack
#check StableMatchingsJointCharging.SM_lt_2078_div_625_pow
#print axioms StableMatchingsJointCharging.SM_lt_2078_div_625_pow
