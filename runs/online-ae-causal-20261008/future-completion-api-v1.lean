import BanditRLProof.OnlineGuessingAECausal
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Filter MeasurableSpace

-- Read-only dependency probe. No new theorem body or source target is proved here.
#check eventuallyMeasurableSpace
#check EventuallyMeasurable
#check MeasurableSpace.measurable_mapNatBool
#check MeasurableSpace.injective_mapNatBool
#check Measurable.measurableEmbedding
#check MeasurableEmbedding.measurable_invFun
#check MeasurableEmbedding.leftInverse_invFun
#check measurable_to_bool
#check measurable_pi_iff
#check eventually_countable_forall
#check ae_all_iff
#check Measurable.aestronglyMeasurable
#check AEStronglyMeasurable.congr
#check Measurable.eventuallyMeasurable_of_eventuallyEq

#check (fun {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : MeasurableSpace Ω) (P : Ω → ℝ) =>
    @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P)
