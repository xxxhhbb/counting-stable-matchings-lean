import StableMatchingsE2E.InfiniteDummyCoupling
import StableMatchingsE2E.ConstantCertificate

namespace StableMatchingsE2E

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval ENNReal BigOperators
open StableMatchings355 StableMatchingsEntropy

noncomputable section

attribute [local instance] Classical.propDecidable

#check MeasurePreserving.lintegral_comp
#check MeasurePreserving.lintegral_comp_emb
#check MeasureTheory.lintegral_map
#check ENNReal.ofReal_tsum_of_nonneg
#check unitInterval.measurePreserving_coe
#check MeasureTheory.lintegral_mono_ae

end

end StableMatchingsE2E
