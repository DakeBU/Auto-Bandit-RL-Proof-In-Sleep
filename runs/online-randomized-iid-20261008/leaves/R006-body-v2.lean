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

/-- Derive joint seed+strict-past current independence from natural whole-process seed independence and target IID. -/
theorem private_seed_past_independent {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ) (t : ℕ) :
    IndepFun (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) (Y t) μ := by
  have hpast : Measurable (fun ω (i : (↑(Finset.range t) : Type)) => Y i ω) :=
    measurable_pi_lambda _ (fun i => hY i)
  have hpc : IndepFun (fun ω (i : (↑(Finset.range t) : Type)) => Y i ω) (Y t) μ := by
    have hi := iIndepFun.indepFun_finset (Finset.range t) {t} (by simp) hind hY
    simpa only [Function.comp_def] using hi.comp measurable_id
      (measurable_pi_apply (⟨t, by simp⟩ : (↑({t} : Finset ℕ) : Type)))
  have hblock : IndepFun S
      (fun ω => ((fun i : (↑(Finset.range t) : Type) => Y i ω), Y t ω)) μ := by
    have he : Measurable (fun y : ℕ → ℝ =>
        ((fun i : (↑(Finset.range t) : Type) => y i), y t)) :=
      (measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) =>
        measurable_pi_apply (i : ℕ))).prodMk (measurable_pi_apply t)
    simpa only [Function.comp_def] using hseed.comp measurable_id he
  exact independent_private_seed_pair μ S _ _ hS hpast (hY t) hblock hpc

/-- Actual generated pre-reveal information grows with the history; no stochastic hypotheses needed. -/
theorem privateSeedPastInformation_monotone
    {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) :
    Monotone (privateSeedPastInformation S Y) := by
  intro s t hst
  let restrict : (Seed × ((↑(Finset.range t) : Type) → ℝ)) →
      (Seed × ((↑(Finset.range s) : Type) → ℝ)) :=
    fun q => (q.1, fun i => q.2 ⟨i, Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp i.property) hst)⟩)
  have hr : Measurable restrict := by
    unfold restrict
    fun_prop
  have hc := MeasurableSpace.comap_mono
    (g := fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) hr.comap_le
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, restrict,
    privateSeedPastInformation] using hc

/-- Any measurable prediction in subordinate information inherits independence; current independence is not supplied. -/
theorem predictable_private_seed_independent {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ) (hP : Measurable[F] P) :
    IndepFun P (Y t) μ := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  have hi : Indep (privateSeedPastInformation S Y t)
      (MeasurableSpace.comap (Y t) inferInstance) μ :=
    (IndepFun_iff_Indep _ _ μ).1 (private_seed_past_independent μ Y hY hind S hS hseed t)
  exact (IndepFun_iff_Indep P (Y t) μ).2
    (indep_of_indep_of_le_left hi (hP.comap_le.trans hF))

/-- Actual jointly measurable policy of seed and finite strict past; empty initial history may use seed. -/
theorem randomized_history_policy_independent {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ)
    (hp : ∀ t, Measurable (policy t)) (t : ℕ) :
    IndepFun (fun ω => policy t (S ω, fun i => Y i ω)) (Y t) μ := by
  have hi := (private_seed_past_independent μ Y hY hind S hS hseed t).comp
    (hp t) measurable_id
  simpa only [Function.comp_def] using hi

/-- General predictable-information actual causal lower producer; derive ambient measurability and L2 from information/support. -/
theorem predictable_private_seed_expectedFixed_excess {Ω : Type u} {Seed : Type v} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ) (hP : ∀ t, Measurable[F t] (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T := by
  have hambient (t : ℕ) : Measurable (prediction t) := by
    have hinfo : privateSeedPastInformation S Y t ≤ ‹MeasurableSpace Ω› :=
      (hS.prodMk (measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) => hY i))).comap_le
    exact Measurable.of_comap_le ((hP t).comap_le.trans ((hF t).trans hinfo))
  have hL (t : ℕ) : MemLp (prediction t) 2 μ :=
    memLp_of_bounded (hpb t) (hambient t).aestronglyMeasurable 2
  have hInd (t : ℕ) : IndepFun (prediction t) (Y t) μ :=
    predictable_private_seed_independent μ Y hY hind S hS hseed t (F t) (hF t)
      (prediction t) (hP t)
  have he : expectedFixedRegret μ Y prediction T =
      ∑ t ∈ Finset.range T, ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ := by
    unfold expectedFixedRegret
    rw [expectedFixedMinimum_eq_variance μ Y hY hlaw hb T]
    exact iid_cumulative_prediction_decomposition μ Y hY hlaw hb prediction hL hInd T
  refine ⟨he, ?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun t _ => integral_nonneg (fun ω => sq_nonneg _))

end BanditRL.OnlineLearning
