import StableMatchings355
import StableMatchings355RandomReveal
import StableMatchingsEntropy
import StableMatchingsProbability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StableMatchingsE2E

open StableMatchings355

/-! Gate 1 smoke checks: the unified project sees both the already-verified
stable-matching structural bridge and the pinned Mathlib analysis stack. -/

#check finite_hasMenJoin
#check exists_full_conditional_support_bridge
#check exists_priority_prefix_full_bridge
#check StableMatchingsEntropy.conditional_index_support_le_extended_marker_window
#check StableMatchingsProbability.DecisionTree.leafCount_le_prod
#check MeasureTheory.Measure.prod
#check intervalIntegral.integral_const
#check Real.log

example : Real.log 1 = 0 := Real.log_one

end StableMatchingsE2E
