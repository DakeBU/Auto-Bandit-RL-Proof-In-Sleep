import BanditRLProof.Algorithms.CUCBOracleSuccess
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual reward integrability and round expectations from the primitive
nonnegative L1 reward law. No bound on realized rewards is imposed. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem integrable_trueScore_comp {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : Ω → A) (hg : Measurable g) :
    Integrable (fun ω => S.score M.trueInput (g ω)) ν := by
  apply (integrable_const (scoreOptimum S.score M.trueInput)).mono'
    ((measurable_of_countable (f:=S.score M.trueInput)).comp hg).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (S.score_nonneg _ _)]
  exact score_le_optimum S.score M.trueInput (g ω)

omit [MeasurableSingletonClass A] in
theorem environment_norm_reward (a : A) :
    (∫z, ‖z.2.2‖ ∂M.environment a)=S.score M.trueInput a := by
  rw [S.score_true]
  apply integral_congr_ae
  filter_upwards [M.reward_nonneg a] with z hz
  exact Real.norm_of_nonneg hz

theorem integrable_round_reward (v : Input m) :
    Integrable (fun z : Round A m => z.2.2.2) (roundKernel S.oracle M.environment v) := by
  apply (ProbabilityTheory.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall (fun a => M.reward_integrable a)
  · simpa only [Kernel.comap_apply, S.environment_norm_reward, id_eq] using
      S.integrable_trueScore_comp (S.oracle v) id measurable_id

omit [MeasurableSingletonClass A] in
theorem round_reward_nonneg (v : Input m) :
    ∀ᵐ z ∂roundKernel S.oracle M.environment v, 0≤z.2.2.2 := by
  apply Kernel.ae_compProd_of_ae_ae (measurableSet_le measurable_const (by fun_prop))
  exact Filter.Eventually.of_forall (fun a => M.reward_nonneg a)

theorem integral_round_reward (v : Input m) :
    (∫z : Round A m, z.2.2.2 ∂roundKernel S.oracle M.environment v)=
      ∫a, S.score M.trueInput a ∂S.oracle v := by
  rw [roundKernel, ProbabilityTheory.integral_compProd (S.integrable_round_reward v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => (S.score_true a).symm)

theorem integral_round_norm_reward_le (v : Input m) :
    (∫z : Round A m, ‖z.2.2.2‖ ∂roundKernel S.oracle M.environment v)≤
      scoreOptimum S.score M.trueInput := by
  have he : (∫z : Round A m, ‖z.2.2.2‖ ∂roundKernel S.oracle M.environment v)=
      ∫z : Round A m, z.2.2.2 ∂roundKernel S.oracle M.environment v := by
    apply integral_congr_ae
    filter_upwards [S.round_reward_nonneg v] with z hz
    exact Real.norm_of_nonneg hz
  rw [he, S.integral_round_reward]
  have h := integral_mono (S.integrable_trueScore_comp (S.oracle v) id measurable_id)
    (integrable_const (scoreOptimum S.score M.trueInput)) (score_le_optimum S.score M.trueInput)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem integral_round_reward_eq_score (v : Input m) :
    (∫z : Round A m, z.2.2.2 ∂roundKernel S.oracle M.environment v)=
      ∫z : Round A m, S.score M.trueInput z.1 ∂roundKernel S.oracle M.environment v := by
  have he := integral_map (μ:=roundKernel S.oracle M.environment v) measurable_fst.aemeasurable
    (measurable_of_countable (f:=S.score M.trueInput)).aestronglyMeasurable
  rw [roundKernel_action_law] at he
  exact (S.integral_round_reward v).trans he

theorem integrable_joint_reward {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : Ω → Input m) (hg : Measurable g) :
    Integrable (fun p : Ω × Round A m => p.2.2.2.2)
      (ν ⊗ₘ (roundKernel S.oracle M.environment).comap g hg) := by
  apply (Measure.integrable_compProd_iff
    (show Measurable (fun p : Ω × Round A m => p.2.2.2.2) by fun_prop).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun ω => S.integrable_round_reward (g ω))
  · apply (integrable_const (scoreOptimum S.score M.trueInput)).mono'
      ((by fun_prop : StronglyMeasurable (fun z : Round A m => ‖z.2.2.2‖)).integral_kernel).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact S.integral_round_norm_reward_le (g ω)

theorem integral_joint_reward_eq_score {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : Ω → Input m) (hg : Measurable g) :
    (∫p : Ω × Round A m, p.2.2.2.2 ∂(ν ⊗ₘ (roundKernel S.oracle M.environment).comap g hg))=
      ∫p : Ω × Round A m, S.score M.trueInput p.2.1
        ∂(ν ⊗ₘ (roundKernel S.oracle M.environment).comap g hg) := by
  rw [Measure.integral_compProd (S.integrable_joint_reward ν g hg),
    Measure.integral_compProd (S.integrable_trueScore_comp
      (ν ⊗ₘ (roundKernel S.oracle M.environment).comap g hg) (fun p => p.2.1) (by fun_prop))]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => S.integral_round_reward_eq_score (g ω)))

end BanditRLProof.CUCB.SourceModel
