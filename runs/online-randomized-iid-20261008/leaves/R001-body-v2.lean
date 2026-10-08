import BanditRLProof.OnlineGuessingIIDBenchmark

open MeasureTheory ProbabilityTheory
universe u v w z

namespace BanditRL.OnlineLearning

/-- Information available before round t: one private tape and strict-past targets. -/
def privateSeedPastInformation {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance

/-- Joint seed independence and X/Y independence produce the regrouped independent blocks. -/
theorem independent_private_seed_pair
    {Ω : Type u} {Seed : Type v} {Χ : Type w} {Ζ : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Seed] [MeasurableSpace Χ] [MeasurableSpace Ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Seed) (X : Ω → Χ) (Y : Ω → Ζ)
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hseed : IndepFun S (fun ω => (X ω, Y ω)) μ) (hXY : IndepFun X Y μ) :
    IndepFun (fun ω => (S ω, X ω)) Y μ := by
  have hSX : IndepFun S X μ := by
    simpa only [Function.comp_def] using hseed.comp measurable_id measurable_fst
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hS.prodMk hX).aemeasurable hY.aemeasurable).2
  rw [(indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hX.aemeasurable).1 hSX]
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable ((hS.prodMk hX).prodMk hY)]
  change μ.map (fun ω => (S ω, (X ω, Y ω))) =
    Measure.map MeasurableEquiv.prodAssoc (((μ.map S).prod (μ.map X)).prod (μ.map Y))
  rw [(indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable
    (hX.prodMk hY).aemeasurable).1 hseed,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
    Measure.prodAssoc_prod]

end BanditRL.OnlineLearning
