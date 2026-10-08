import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Topology.UnitInterval

open MeasureTheory ProbabilityTheory

universe u v
namespace BanditRL.OnlineLearning


/-! Derived AE strict-past information infrastructure for Orabona v10 printed1/PDF13 and printed3/PDF15. A classical measurable version, not off-null identity or an executable learner constructor. Full completed-information and universal stochastic-kernel coverage remain separate required obligations. -/

theorem ae_predictable_exists_bounded_history_policy {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (S : Ω → Seed)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, AEStronglyMeasurable[F t] (prediction t) μ)
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) :
    ∃ policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂μ, ∀ t, prediction t ω = policy t (S ω, fun i => Y i ω) := by
  classical
  have hfactor (t : ℕ) :
      ∃ f : (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
        Measurable f ∧ (hP t).mk (prediction t) =
          fun ω => f (S ω, fun i => Y i ω) := by
    have hm : Measurable[privateSeedPastInformation S Y t] ((hP t).mk (prediction t)) :=
      Measurable.of_comap_le ((hP t).measurable_mk.comap_le.trans (hF t))
    change Measurable[MeasurableSpace.comap
      (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω)) inferInstance] _ at hm
    obtain ⟨f, hf, he⟩ := hm.exists_eq_measurable_comp
    exact ⟨f, hf, by simpa only [Function.comp_def] using he⟩
  choose f hf he using hfactor
  let policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ :=
    fun t q => (Set.projIcc (0 : ℝ) 1 zero_le_one (f t q) : ℝ)
  refine ⟨policy, ?_, ?_, ?_⟩
  · intro t
    exact ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).measurable.comp
      (hf t)).subtype_coe
  · intro t q
    exact (Set.projIcc (0 : ℝ) 1 zero_le_one (f t q)).property
  · apply ae_all_iff.2
    intro t
    filter_upwards [(hP t).ae_eq_mk, hpb t] with ω hω hbω
    have hq : f t (S ω, fun i => Y i ω) = prediction t ω :=
      (congrFun (he t) ω).symm.trans hω.symm
    change prediction t ω = (Set.projIcc (0 : ℝ) 1 zero_le_one
      (f t (S ω, fun i => Y i ω)) : ℝ)
    rw [hq, Set.projIcc_of_mem zero_le_one hbω]

theorem ae_predictable_private_seed_independent {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ) (hP : AEStronglyMeasurable[F] P μ) :
    IndepFun P (Y t) μ := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  have hi := predictable_private_seed_independent μ Y hY hind S hS hseed t F hF
    (hP.mk P) hP.measurable_mk
  exact hi.congr hP.ae_eq_mk.symm (Filter.EventuallyEq.refl _ _)

theorem ae_predictable_private_seed_expectedFixed_excess {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, AEStronglyMeasurable[F t] (prediction t) μ)
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T := by
  have hinfo (t : ℕ) : privateSeedPastInformation S Y t ≤ ‹MeasurableSpace Ω› :=
    (hS.prodMk (measurable_pi_lambda _ (fun i : (↑(Finset.range t) : Type) => hY i))).comap_le
  have hL (t : ℕ) : MemLp (prediction t) 2 μ :=
    memLp_of_bounded (hpb t)
      (AEStronglyMeasurable.mono ((hF t).trans (hinfo t)) (hP t)) 2
  have hInd (t : ℕ) : IndepFun (prediction t) (Y t) μ :=
    ae_predictable_private_seed_independent μ Y hY hind S hS hseed t (F t) (hF t)
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
